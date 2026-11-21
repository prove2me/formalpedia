-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scalar_moment_exp
-- name    : Kyprianou.Ch08.StageB.source_result81_scalar_moment_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T14:18:29.599786+00:00
-- url     : https://prove2.me/theorems/c4a42425-fc50-48cc-acac-5a63a6d6c4d2
-- title:
--   A positive finite multiplicative moment is exponential in time
-- statement:
--   The logarithm of a finite positive multiplicative moment is additive. Extend its rational time formula using approximations from the right and the Fatou inequality. Additivity with an integer endpoint gives the reverse inequality. This is the scalar time-scaling step of the actual Lévy moment.
-- source:
--   Kyprianou (2006), Ch. 3 and Ch. 8 exponential moments. Isolates the scalar convergence in theorem 7a841a62-55e9-4628-8737-7128864357b2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scalar_moment_exp
    (G : ℝ≥0 → ℝ≥0∞) (hG0 : G 0 = 1)
    (hmul : ∀ s u, G (s + u) = G s * G u)
    (hne : ∀ s, G s ≠ 0) (hfin : ∀ s, G s ≠ ⊤)
    (hright : ∀ (s : ℝ≥0) (sn : ℕ → ℝ≥0),
      (∀ n, s ≤ sn n) → Tendsto sn atTop (nhds s) →
        G s ≤ Filter.liminf (fun n => G (sn n)) atTop)
    (t : ℝ≥0) :
    (G t).toReal = Real.exp ((t : ℝ) * Real.log (G 1).toReal) := by
  sorry
