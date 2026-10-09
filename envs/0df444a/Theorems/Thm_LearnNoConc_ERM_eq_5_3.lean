-- Prove2me | Theorems.Thm_LearnNoConc_ERM_eq_5_3
-- name    : LearnNoConc.ERM.eq_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:51:02.79181+00:00
-- url     : https://prove2.me/theorems/274f015f-2a4a-49a2-a67a-683431ccec9a
-- title:
--   (5.3), p. 23 — w.p. ≥ 1 − 2exp(−NQ²_{F−F}(2τ)/2): ‖f − f*‖ ≥ r ⇒ N⁻¹Σ(f − f*)²(X_i) ≥ (τ²/4)Q_{F−F}(2τ)‖f − f*‖²
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $F\subset L_2(\mu)$ a closed, convex class of measurable functions, $f^*\in F$, and $H=F-f^*$. Assume that $\tau>0$ satisfies $Q_{F-F}(2\tau)>0$. Let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. with law $\mu$. If $r>\beta_N(H,\tau Q_{F-F}(2\tau)/16)$, then with probability at least $1-2\exp(-NQ_{F-F}^2(2\tau)/2)$, every $f\in F$ with $\|f-f^*\|_{L_2}\ge r$ satisfies
--
--   $$\frac1N\sum_{i=1}^N(f-f^*)^2(X_i)\ge\frac{\tau^2}{4}\,Q_{F-F}(2\tau)\cdot\|f-f^*\|_{L_2}^2.\tag{5.3}$$
--
--   This is the quadratic lower bound on the empirical excess loss that controls the low-noise regime in Theorem 3.1.
--
--   **Formalization Note** The conclusion bounds the (outer) probability of the event that some $f\in F$ with $\|f-f^*\|_{L_2}\ge r$ violates (5.3). Measurability of every $f\in F$ and pointwise separability of $F$ are added, as in Theorem 5.3.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, proof of Theorem 3.1, display (5.3), p. 23

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Display (5.3), p. 23: with probability at least `1 − 2 exp(−N Q²_{F−F}(2τ)/2)`, every
`f ∈ F` with `‖f − f*‖_{L₂} ≥ r` satisfies
`(1/N) ∑ (f − f*)²(X_i) ≥ (τ²/4) Q_{F−F}(2τ) ‖f − f*‖²_{L₂}`, for `r > β_N(F − f*, τ Q_{F−F}(2τ)/16)`. -/
theorem eq_5_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Set (Ω → ℝ)) (hFm : ∀ f ∈ F, Measurable f) (hF2 : ∀ f ∈ F, MemLp f 2 μ)
    (hFconv : Convex ℝ F) (hFcl : IsL2Closed μ F) (hFsep : PointwiseSeparable μ F)
    (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q μ (diffSet F) (2 * τ))
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F) (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : betaN μ (shift F fstar) N (τ * Q μ (diffSet F) (2 * τ) / 16)
      < ENNReal.ofReal r) :
    (Measure.pi fun _ : Fin N => μ)
      {x | ∃ f ∈ F, ENNReal.ofReal r ≤ eLpNorm (f - fstar) 2 μ ∧
          (∑ i, (f (x i) - fstar (x i)) ^ 2) / N
            < τ ^ 2 / 4 * Q μ (diffSet F) (2 * τ) * ((eLpNorm (f - fstar) 2 μ).toReal) ^ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(N * Q μ (diffSet F) (2 * τ) ^ 2 / 2))) := by sorry

end LearnNoConc.ERM
