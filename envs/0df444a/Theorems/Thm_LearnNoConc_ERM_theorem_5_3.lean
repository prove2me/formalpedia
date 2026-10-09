-- Prove2me | Theorems.Thm_LearnNoConc_ERM_theorem_5_3
-- name    : LearnNoConc.ERM.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:01.512726+00:00
-- url     : https://prove2.me/theorems/91308ce7-fc0d-4541-b3b1-c30afcb3d8eb
-- title:
--   Theorem 5.3, p. 21 — (5.1): ‖f − f*‖ ≥ r > β_N(H, τQ_H(2τ)/16) ⇒ |{i : |(f − f*)(X_i)| ≥ τ‖f − f*‖}| ≥ NQ_H(2τ)/4, H = F − f*
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $F\subset L_2(\mu)$ a closed, convex class of measurable functions. Assume that $\tau>0$ satisfies $Q_{F-F}(2\tau)>0$. Given $f^*\in F$, set $H=F-f^*$. Let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. with law $\mu$. Then for every $r>\beta_N(H,\tau Q_H(2\tau)/16)$, with probability at least $1-2\exp(-NQ_H^2(2\tau)/2)$, every $f\in F$ with $\|f-f^*\|_{L_2}\ge r$ satisfies
--
--   $$\bigl|\{i:|(f-f^*)(X_i)|\ge\tau\|f-f^*\|_{L_2}\}\bigr|\ge N\,\frac{Q_H(2\tau)}{4}.\tag{5.1}$$
--
--   Here $f^*$ is any element of $F$. The result is the quadratic ("version space") half of the proof of Theorem 3.1.
--
--   **Formalization Note** The conclusion bounds the (outer) probability of the event that some $f\in F$ with $\|f-f^*\|_{L_2}\ge r$ violates (5.1). Closedness is in $L_2(\mu)$. Measurability of every $f\in F$ and pointwise separability of $F$ are added; the latter stands in for the measurability of suprema that the paper takes for granted. The hypothesis is on $Q_{F-F}$ while the radius and the conclusion use $Q_H$, as printed.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, Theorem 5.3, p. 21

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Theorem 5.3, p. 21: the estimate (5.1) for `H = F − f*`, `F` closed and convex. -/
theorem theorem_5_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Set (Ω → ℝ)) (hFm : ∀ f ∈ F, Measurable f) (hF2 : ∀ f ∈ F, MemLp f 2 μ)
    (hFconv : Convex ℝ F) (hFcl : IsL2Closed μ F) (hFsep : PointwiseSeparable μ F)
    (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q μ (diffSet F) (2 * τ))
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F) (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : betaN μ (shift F fstar) N (τ * Q μ (shift F fstar) (2 * τ) / 16)
      < ENNReal.ofReal r) :
    (Measure.pi fun _ : Fin N => μ)
      {x | ∃ f ∈ F, ENNReal.ofReal r ≤ eLpNorm (f - fstar) 2 μ ∧
          ((Finset.univ.filter fun i =>
              τ * (eLpNorm (f - fstar) 2 μ).toReal ≤ |f (x i) - fstar (x i)|).card : ℝ)
            < N * Q μ (shift F fstar) (2 * τ) / 4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(N * Q μ (shift F fstar) (2 * τ) ^ 2 / 2))) := by sorry

end LearnNoConc.ERM
