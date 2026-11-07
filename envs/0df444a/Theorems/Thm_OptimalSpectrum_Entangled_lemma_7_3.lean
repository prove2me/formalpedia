-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_7_3
-- name    : OptimalSpectrum.Entangled.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:38.433193+00:00
-- url     : https://prove2.me/theorems/0583e467-a49d-4d05-a151-96a59e165142
-- title:
--   Lemma 7.3 — variance in terms of the derivative operators $\Theta^{(r)}_p$
-- statement:
--   Let $1\le k\le n$ and let $p$ be a real polynomial of degree at most $k$. Let $\overline\Pi$ be an orthogonal projector, $\rho$ a density matrix on $\mathbb C^d$, $\sigma=\overline\Pi\rho\overline\Pi$, and for $1\le r\le k$ let $\Theta^{(r)}_p$ be the operator on $(\mathbb C^d)^{\otimes r}$ with $\mathrm{tr}[\Theta^{(r)}_p(H_1\otimes\cdots\otimes H_r)]=D^{(r)}_p(H_1,\dots,H_r)$ for all Hermitian $H_j$ (Eq. (40)). Then
--
--   1. for the conditioned uniform POVM, $\widehat F_p=g_p(X_1,\dots,X_n)$ with i.i.d. single-copy estimators,
--   $$\mathrm{Var}(\widehat F_p)\le\sum_{r=1}^k\frac{3^r}{r!\,n^{\downarrow r}}\big\|\Theta^{(r)}_p\big\|_{\mathrm{HS}}^2;\tag{41}$$
--   2. for weak Schur sampling, $\widehat F_p$ the measured value of $F_p$ on $\rho^{\otimes n}$,
--   $$\mathrm{Var}(\widehat F_p)\le\sum_{r=1}^k\frac1{r!\,n^{\downarrow r}}\big\|\Theta^{(r)}_p(\sqrt\sigma)^{\otimes r}\big\|_{\mathrm{HS}}^2.\tag{42}$$
--
--   The variances are thereby reduced to norms of the derivative operators, which Lemma 7.9 bounds.
--
--   Differences from the source:
--   - encoding: Θ_p^(r) defined by Eq. (40) → any family Θ r satisfying Eq. (40) for all Hermitian directions, 1 ≤ r ≤ k; reason: Eq. (40) determines Θ_p^(r) uniquely, as the page says
--   - reading: Var(F̂_p) for weak Schur sampling → tr(F_p² ρ^⊗n) − tr(F_p ρ^⊗n)²; reason: the paper's formula for the variance of measuring an observable (pp. 6, 24); the M_m commute, so this is the variance of the joint measurement
--   - encoding: "the conditioned uniform POVM" and its i.i.d. estimators X_i → independent outcomes U_i with law (1 − tr σ)δ_0 + d⟨u|σ|u⟩U(du), X_i = X(U_i), and the variance of g_p(X_1,…,X_n); reason: the discarded outcome is recorded as the zero vector; this is the law of §7.1–7.1.1
--   - encoding: Π̄ the small-bucket projector, σ = Π̄ρΠ̄ (§7 setting) → an orthogonal projector Pbar and a density matrix ρ as binders, σ = Pbar ρ Pbar; √σ the functional-calculus square root; reason: standing setting of §7
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.3, Eqs. (41)–(42), p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily
import Definitions.Def_OptimalSpectrum_Entangled_derivOp
import Definitions.Def_OptimalSpectrum_Entangled_hsNormSq
import Definitions.Def_OptimalSpectrum_Entangled_condUniformX
import Definitions.Def_OptimalSpectrum_Entangled_gPoly
import Definitions.Def_OptimalSpectrum_Entangled_IsCondUniformSample
import Definitions.Def_OptimalSpectrum_Entangled_entVar

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace OptimalSpectrum.Entangled

/-- **Lemma 7.3 (Variance in terms of derivative operators).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.3, printed p. 22 (PDF p. 24): "Let 1 ⩽ k ⩽ n, and let p be a polynomial of degree at
most k. For the conditioned uniform POVM, Var(F̂_p) ⩽ ∑_(r=1)^k (3^r/(r! n^↓r)) ∥Θ_p^(r)∥²_HS. (41) For
weak Schur sampling, Var(F̂_p) ⩽ ∑_(r=1)^k (1/(r! n^↓r)) ∥Θ_p^(r)(√σ)^⊗r∥²_HS. (42)"

Setting of §7 (printed pp. 19–21): `Π̄` is the small-bucket projector (an orthogonal projector),
`ρ` a density matrix, `σ = Π̄ρΠ̄`. `Θ_p^(r)` is the operator on `(ℂ^d)^{⊗r}` with
`tr[Θ_p^(r)(H₁ ⊗ ⋯ ⊗ H_r)] = D_p^(r)(H₁, …, H_r)` for all Hermitian `H_j` (Eq. (40)), which determines
it uniquely.
1. (41) For `n` i.i.d. outcomes of the conditioned uniform POVM, `F̂_p = g_p(X₁, …, X_n)` (Eq. (36)).
2. (42) For weak Schur sampling, `F̂_p` is the measured value of `F_p` in `ρ^{⊗n}`, with variance
   `tr(F_p² ρ^{⊗n}) − tr(F_p ρ^{⊗n})²`.

**Formalization Note.** `Θ_p^(r)` is any family satisfying (40) for `1 ≤ r ≤ k` (it is unique).
`√σ` is the continuous-functional-calculus square root. `F̂_p` in (41) is bounded (each `X_i` is), so
its variance is finite and `variance` is not a junk value. -/
theorem lemma_7_3 (d n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ k) (Pbar ρ : Matrix (Fin d) (Fin d) ℂ) (hP : Pbar.IsHermitian)
    (hP2 : Pbar * Pbar = Pbar) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (Θ : (r : ℕ) → Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hΘ : ∀ r, 1 ≤ r → r ≤ k → ∀ H : Fin r → Matrix (Fin d) (Fin d) ℂ, (∀ j, (H j).IsHermitian) →
      Matrix.trace (Θ r * kronFamily H) = (derivOp p (Pbar * ρ * Pbar) r H : ℂ)) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Fin n → Ω → EuclideanSpace ℂ (Fin d)),
        IsCondUniformSample P (Pbar * ρ * Pbar) U →
        variance (fun ω => gPoly d n p fun i => condUniformX d (U i ω)) P ≤
          ∑ r ∈ Finset.Icc 1 k,
            (3 : ℝ) ^ r / ((r.factorial : ℝ) * n.descFactorial r) * hsNormSq (Θ r)) ∧
    entVar d n Pbar p ρ ≤
      ∑ r ∈ Finset.Icc 1 k, 1 / ((r.factorial : ℝ) * n.descFactorial r) *
        hsNormSq (Θ r * QAlgorithms.piKron r (CFC.sqrt (Pbar * ρ * Pbar))) := by sorry

end OptimalSpectrum.Entangled
