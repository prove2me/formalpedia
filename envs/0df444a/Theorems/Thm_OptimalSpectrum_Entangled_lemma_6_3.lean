-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_6_3
-- name    : OptimalSpectrum.Entangled.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:59.463435+00:00
-- url     : https://prove2.me/theorems/13cece74-3f6d-48d0-b2ad-ce6672e87ab1
-- title:
--   Lemma 6.3 — Jackson approximation near the endpoints
-- statement:
--   There is a universal constant $C>0$ with the following property. For every $K\ge1$ there are damping factors $\eta_1,\dots,\eta_K\in[0,1]$, depending only on $K$ and the index, such that for every 1-Lipschitz $f:[-1,1]\to\mathbb R$ with Chebyshev coefficients $\gamma_k$, the polynomial $Q_f(t)=\gamma_0+\sum_{k=1}^K\eta_k\gamma_kT_k(t)$ satisfies
--
--   $$|f(t)-Q_f(t)|\le C\Big(\frac{\sqrt{1-t^2}}K+\frac1{K^2}\Big),\qquad t\in[-1,1],$$
--
--   and, if $f(-1)=0$, the anchored polynomial $P_f(t)=\sum_{k=1}^K\eta_k\gamma_k\big(T_k(t)-(-1)^k\big)$ satisfies
--
--   $$|f(t)-P_f(t)|\le C\,\frac{\sqrt{1+t}}K,\qquad t\in[-1,1].$$
--
--   The bound improves to $O(1/K^2)$ at the endpoints of the interval, and the anchored version vanishes at $-1$; this is what makes the full-interval recovery bound of Proposition 6.1 depend on $\sqrt{dL}$ instead of $dL$.
--
--   Differences from the source:
--   - encoding: f : [−1, 1] → R → f : ℝ → ℝ, 1-Lipschitz on [−1, 1]; reason: only the values on [−1, 1] enter the statement and the coefficients
--   - encoding: "the Chebyshev expansion of f" with coefficients γ_k → γ_k given by the weighted integrals (1/π)∫ f/√(1−t²) and (2/π)∫ f T_k/√(1−t²); reason: these are the coefficients of the expansion; its convergence is not part of the claim
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 6.3, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_chebCoeff

namespace OptimalSpectrum.Entangled

/-- **Lemma 6.3 (Jackson approximation near the endpoints).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 6.3, printed p. 15 (PDF p. 17): "Let f : [−1, 1] → R be 1-Lipschitz and let K ⩾ 1.
Write the Chebyshev expansion of f as f(t) = γ₀ + ∑_(k⩾1) γ_k T_k(t). There exist damping factors
η₁, …, η_K ∈ [0, 1], depending only on K and the coefficient index, such that the polynomial
Q_f(t) = γ₀ + ∑_(k=1)^K a_k T_k(t), a_k = η_k γ_k, satisfies
|f(t) − Q_f(t)| ⩽ C(√(1 − t²)/K + 1/K²), t ∈ [−1, 1]. Moreover, if f(−1) = 0, the anchored polynomial
P_f(t) = Q_f(t) − Q_f(−1) = ∑_(k=1)^K a_k(T_k(t) − (−1)^k) satisfies |f(t) − P_f(t)| ⩽ C√(1 + t)/K,
t ∈ [−1, 1]. Here C is a universal constant."

**Formalization Note.** `γ_k` are the Chebyshev coefficients `chebCoeff f k`. The quantifier order
`∃ C, ∀ K, ∃ η, ∀ f` makes `C` universal and the damping factors independent of `f`. `f` is a real
function that is 1-Lipschitz on `[−1, 1]`; only its values there matter. -/
theorem lemma_6_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
      ∃ η : ℕ → ℝ, (∀ k, 1 ≤ k → k ≤ K → η k ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ f : ℝ → ℝ, LipschitzOnWith 1 f (Set.Icc (-1) 1) →
          (∀ t ∈ Set.Icc (-1 : ℝ) 1,
            |f t - (chebCoeff f 0 + ∑ k ∈ Finset.Icc 1 K,
                η k * chebCoeff f k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t)| ≤
              C * (Real.sqrt (1 - t ^ 2) / K + 1 / (K : ℝ) ^ 2)) ∧
          (f (-1) = 0 → ∀ t ∈ Set.Icc (-1 : ℝ) 1,
            |f t - ∑ k ∈ Finset.Icc 1 K,
                η k * chebCoeff f k * ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t - (-1) ^ k)| ≤
              C * Real.sqrt (1 + t) / K) := by sorry

end OptimalSpectrum.Entangled
