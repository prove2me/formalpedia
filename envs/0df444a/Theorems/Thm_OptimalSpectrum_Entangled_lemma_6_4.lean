-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_6_4
-- name    : OptimalSpectrum.Entangled.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:02.755911+00:00
-- url     : https://prove2.me/theorems/6dbb3bdd-c323-4749-971b-301a8d86d47f
-- title:
--   Lemma 6.4 — coefficient energy of the Jackson approximations
-- statement:
--   There is a universal constant $C>0$ such that for every $L>0$, $K\ge1$ and every 1-Lipschitz $f:[0,L]\to\mathbb R$ with $f(0)=0$ the following holds for both bases. There are coefficients $a_1,\dots,a_K$ with
--
--   $$\Big|f(x)-\sum_{k=1}^Ka_k\phi_k(x)\Big|\le C\frac{\sqrt{Lx}}K\quad(x\in[0,L]),\qquad \sum_{k=1}^Kk^2a_k^2\le CL\int_0^L|f'(x)|^2\,dx,$$
--
--   and coefficients $a_1,\dots,a_K$ with
--
--   $$\Big|f(x)-\sum_{k=1}^Ka_k\psi_k(x)\Big|\le C\frac LK\quad(x\in[0,L]),\qquad \sum_{k=1}^Kk^2a_k^2\le CL\int_0^L|f'(x)|^2\,dx,$$
--
--   where $f'$ is the almost-everywhere derivative of $f$. The coefficient bound (30) controls how much moment errors are amplified when the test function of the Kantorovich–Rubinstein duality is replaced by its polynomial approximation.
--
--   Differences from the source:
--   - encoding: f : [0, L] → R and its almost-everywhere derivative f′ → f : ℝ → ℝ, 1-Lipschitz on [0, L], with deriv f; reason: only values on [0, L] matter; deriv f is the derivative wherever it exists, which by Rademacher is almost every point of (0, L)
--   - encoding: L > 0 and K ⩾ 1 stated once in the §6 Setup → L > 0 and 1 ≤ K as binders; reason: standing assumptions of the section
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 6.4, Eq. (30), p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_phiPoly
import Definitions.Def_OptimalSpectrum_Entangled_psiPoly

namespace OptimalSpectrum.Entangled

/-- **Lemma 6.4 (Coefficient energy of the Jackson approximations).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 6.4, printed p. 17 (PDF p. 19): "Let f : [0, L] → R be 1-Lipschitz with f(0) = 0. For
either choice q_k = ϕ_k for all k or q_k = ψ_k for all k, there exists a polynomial
P_f(x) = ∑_(k=1)^K a_k q_k(x) such that, for every x ∈ [0, L], |f(x) − P_f(x)| ⩽ C√(Lx)/K for q_k = ϕ_k,
and CL/K for q_k = ψ_k, and ∑_(k=1)^K k² a_k² ⩽ CL ∫_0^L |f′(x)|² dx. (30) Here f′ denotes the
almost-everywhere derivative of f."

**Formalization Note.** `L > 0` and `K ≥ 1` are the standing assumptions of §6 (Setup, printed
p. 13). `C` is universal (before `L`, `K`, `f`). `f` is a real function, 1-Lipschitz on `[0, L]`;
`deriv f` is its derivative wherever it exists, which by Rademacher's theorem is almost every point
of `(0, L)`, so the integral is that of the a.e. derivative. -/
theorem lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ K : ℕ, 1 ≤ K → ∀ f : ℝ → ℝ,
      LipschitzOnWith 1 f (Set.Icc 0 L) → f 0 = 0 →
      (∃ a : ℕ → ℝ,
          (∀ x ∈ Set.Icc 0 L,
            |f x - ∑ k ∈ Finset.Icc 1 K, a k * (phiPoly L k).eval x| ≤ C * Real.sqrt (L * x) / K) ∧
          ∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ 2 * a k ^ 2 ≤ C * L * ∫ x in (0 : ℝ)..L, |deriv f x| ^ 2) ∧
      (∃ a : ℕ → ℝ,
          (∀ x ∈ Set.Icc 0 L,
            |f x - ∑ k ∈ Finset.Icc 1 K, a k * (psiPoly L k).eval x| ≤ C * L / K) ∧
          ∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ 2 * a k ^ 2 ≤ C * L * ∫ x in (0 : ℝ)..L, |deriv f x| ^ 2) := by sorry

end OptimalSpectrum.Entangled
