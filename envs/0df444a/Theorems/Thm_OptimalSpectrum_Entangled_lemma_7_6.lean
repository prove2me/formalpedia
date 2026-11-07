-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_7_6
-- name    : OptimalSpectrum.Entangled.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:07.753069+00:00
-- url     : https://prove2.me/theorems/dd530801-96ce-4327-a11e-d9d0a1fa6a3e
-- title:
--   Lemma 7.6 — variance bound from the quantum Efron–Stein decomposition
-- statement:
--   Let $\mathcal H=\mathbb C^\iota$ be a finite-dimensional Hilbert space, $\rho$ a density matrix on $\mathcal H$, and $G$ a Hermitian operator on $\mathcal H^{\otimes n}$ commuting with every permutation of the tensor factors. Put $f_G(A)=\mathrm{tr}(GA^{\otimes n})$. For $1\le r\le n$ let $K_r$ be a permutation-invariant Hermitian operator on $\mathcal H^{\otimes r}$ with
--
--   $$\mathrm{tr}\big[K_r(H_1\otimes\cdots\otimes H_r)\big]=\frac1{n^{\downarrow r}}\frac{\partial^r}{\partial t_1\cdots\partial t_r}f_G\Big(\rho+\sum_{j=1}^rt_jH_j\Big)\Big|_{t_1=\cdots=t_r=0}\tag{47}$$
--
--   for all traceless Hermitian $H_1,\dots,H_r$. Then
--
--   $$\mathrm{tr}(G^2\rho^{\otimes n})-\mathrm{tr}(G\rho^{\otimes n})^2\le\sum_{r=1}^n\binom nr\mathrm{tr}\big(K_r^2\rho^{\otimes r}\big).$$
--
--   The left side is the variance of measuring $G$ on $\rho^{\otimes n}$. The lemma reduces the variance of the entangled moment estimate to derivatives of $A\mapsto\mathrm{tr}\,p(A)$.
--
--   Differences from the source:
--   - reading: ρ ∈ D(H) "for some Hilbert space H" → H = ℂ^ι for an arbitrary finite index type ι; reason: the page takes traces of G, K_r and treats f_G as a polynomial with no trace-class provisos, and applies the lemma to ℂ^d; there is no infinite-dimensional statement without invented hypotheses
--   - encoding: f_G(A) = tr(GA^⊗n) and ∂^r/∂t_1⋯∂t_r → real part of the trace; the r-th Fréchet derivative at 0 on the coordinate directions; reason: the trace is real on Hermitian arguments, and the mixed partial of a polynomial in t is this derivative
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.6, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily
import Definitions.Def_OptimalSpectrum_Entangled_mixedPartial

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **Lemma 7.6 (Variance bound from the quantum Efron–Stein decomposition).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.6, printed p. 24 (PDF p. 26): "Let ρ ∈ D(H) for some Hilbert space H, and let G be an
observable on H^⊗n invariant under permutations of the tensor factors. Define f_G(A) := tr(GA^⊗n).
For any 1 ⩽ r ⩽ n, choose a permutation-invariant Hermitian operator K_r on H^⊗r satisfying
tr[K_r(H₁ ⊗ ⋯ ⊗ H_r)] = (1/n^↓r) ∂^r/∂t₁⋯∂t_r f_G(ρ + ∑_(j=1)^r t_j H_j)|_(t₁=⋯=t_r=0) (47) for all
traceless Hermitian H₁, …, H_r. Then the variance of measuring G in state ρ^⊗n satisfies
tr(G²ρ^⊗n) − tr(Gρ^⊗n)² ⩽ ∑_(r=1)^n (n choose r) tr(K_r² ρ^⊗r)."

**Formalization Note.** `H = ℂ^ι` for an arbitrary finite index type `ι` (the paper takes traces of
operators on `H^⊗n` with no trace-class provisos, and applies the lemma to `ℂ^d`). `f_G` is
evaluated through the real part of the trace, which is the trace itself on the Hermitian arguments.
`K_r` is given for `1 ≤ r ≤ n` as a family `Kop r`. -/
theorem lemma_7_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (ρ : Matrix ι ι ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (G : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hG : G.IsHermitian) (hGperm : ∀ π : Equiv.Perm (Fin n), permOp π * G = G * permOp π)
    (Kop : (r : ℕ) → Matrix (Fin r → ι) (Fin r → ι) ℂ)
    (hKherm : ∀ r, 1 ≤ r → r ≤ n → (Kop r).IsHermitian)
    (hKperm : ∀ r, 1 ≤ r → r ≤ n → ∀ π : Equiv.Perm (Fin r), permOp π * Kop r = Kop r * permOp π)
    (hK : ∀ r, 1 ≤ r → r ≤ n → ∀ H : Fin r → Matrix ι ι ℂ,
      (∀ j, (H j).IsHermitian ∧ Matrix.trace (H j) = 0) →
      Matrix.trace (Kop r * kronFamily H) =
        (((1 / (n.descFactorial r : ℝ)) * mixedPartial r fun t =>
          (Matrix.trace (G * QAlgorithms.piKron n (ρ + ∑ j, t j • H j))).re : ℝ) : ℂ)) :
    (Matrix.trace (G * G * QAlgorithms.piKron n ρ)).re -
        (Matrix.trace (G * QAlgorithms.piKron n ρ)).re ^ 2 ≤
      ∑ r ∈ Finset.Icc 1 n,
        (n.choose r : ℝ) * (Matrix.trace (Kop r * Kop r * QAlgorithms.piKron r ρ)).re := by sorry

end OptimalSpectrum.Entangled
