-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_weighted_lipschitz_path_has_measurable_drift_density
-- name    : ManyServerQED.Scheduling.weighted_lipschitz_path_has_measurable_drift_density
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:38:46.336971+00:00
-- url     : https://prove2.me/theorems/9b3cb0f3-fc72-4d0f-a1f0-659a415c4e8f
-- title:
--   Measurable drift of a weighted Lipschitz vector path
-- statement:
--   Let $A(\omega,t)$ be a jointly measurable vector path and let $R(\omega,t)$ be a nonnegative jointly measurable scalar function continuous in time. If an increment of $A$ is bounded by its interval length times every upper bound for $R$ on that interval, then $A(t)-A(0)$ is the time integral of a jointly measurable density $b$ satisfying $\lVert b(\omega,t)\rVert_\infty\le R(\omega,t)$ at every time.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory
open scoped NNReal

theorem ManyServerQED.Scheduling.weighted_lipschitz_path_has_measurable_drift_density {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (A : Ω → ℝ → (Fin k → ℝ)) (R : Ω → ℝ → ℝ)
    (hA : Measurable (fun z : Ω × ℝ => A z.1 z.2))
    (hR : Measurable (fun z : Ω × ℝ => R z.1 z.2))
    (hRc : ∀ ω, Continuous (R ω)) (hRn : ∀ ω t, 0 ≤ R ω t)
    (hLip : ∀ ω s t C, 0 ≤ s → 0 ≤ t →
      (∀ u ∈ uIcc s t, R ω u ≤ C) → ‖A ω t - A ω s‖ ≤ C*|t-s|) :
    ∃ b : Ω → ℝ → Fin k → ℝ,
      Measurable (fun z : Ω × ℝ => b z.1 z.2) ∧
      (∀ ω t, ‖b ω t‖ ≤ R ω t) ∧
      ∀ ω T, 0 ≤ T → (∫ s in (0:ℝ)..T, b ω s) = A ω T - A ω 0 := by sorry
