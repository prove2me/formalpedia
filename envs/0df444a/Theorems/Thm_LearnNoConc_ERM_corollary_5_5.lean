-- Prove2me | Theorems.Thm_LearnNoConc_ERM_corollary_5_5
-- name    : LearnNoConc.ERM.corollary_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:12.793978+00:00
-- url     : https://prove2.me/theorems/8516656e-ad51-4645-a111-ae5d6dab40cd
-- title:
--   Corollary 5.5, p. 22 — (5.2): star-shaped H, ‖h‖ ≥ r > β_N(H, τQ_H(2τ)/16) ⇒ |{i : |h(X_i)| ≥ τ‖h‖}| ≥ NQ_H(2τ)/4
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $H\subset L_2(\mu)$ a class of measurable functions that is star-shaped around $0$. Let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. with law $\mu$. Assume that $\tau>0$ satisfies $Q_H(2\tau)>0$. Then for every $r>\beta_N(H,\tau Q_H(2\tau)/16)$, with probability at least $1-2\exp(-NQ_H^2(2\tau)/2)$, every $h\in H$ with $\|h\|_{L_2}\ge r$ satisfies
--
--   $$\bigl|\{i:|h(X_i)|\ge\tau\|h\|_{L_2}\}\bigr|\ge N\,\frac{Q_H(2\tau)}{4}.\tag{5.2}$$
--
--   It extends Theorem 5.4 from the unit sphere to all functions of a star-shaped class outside a ball whose radius is set by the localized Rademacher average.
--
--   **Formalization Note** The conclusion bounds the (outer) probability of the event "some $h\in H$ with $\|h\|_{L_2}\ge r$ violates (5.2)". $H\subset L_2(\mu)$ is the standing assumption of Assumption 3.1; measurability of each $h$ and pointwise separability of $H$ are added (the latter stands in for the measurability of suprema the paper takes for granted).
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, Corollary 5.5, p. 22

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Corollary 5.5, p. 22: the uniform empirical small-ball estimate (5.2) for a star-shaped class
above the level `β_N(H, τ Q_H(2τ)/16)`. -/
theorem corollary_5_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Set (Ω → ℝ)) (hHm : ∀ h ∈ H, Measurable h) (hH2 : ∀ h ∈ H, MemLp h 2 μ)
    (hH : StarShaped H) (hHsep : PointwiseSeparable μ H)
    (N : ℕ) (hN : 0 < N) (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q μ H (2 * τ))
    (r : ℝ) (hr : betaN μ H N (τ * Q μ H (2 * τ) / 16) < ENNReal.ofReal r) :
    (Measure.pi fun _ : Fin N => μ)
      {x | ∃ h ∈ H, ENNReal.ofReal r ≤ eLpNorm h 2 μ ∧
          ((Finset.univ.filter fun i => τ * (eLpNorm h 2 μ).toReal ≤ |h (x i)|).card : ℝ)
            < N * Q μ H (2 * τ) / 4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(N * Q μ H (2 * τ) ^ 2 / 2))) := by sorry

end LearnNoConc.ERM
