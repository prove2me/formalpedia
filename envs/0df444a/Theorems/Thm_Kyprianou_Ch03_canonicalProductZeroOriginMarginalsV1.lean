-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalProductZeroOriginMarginalsV1
-- name    : Kyprianou.Ch03.canonicalProductZeroOriginMarginalsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:01:57.723811+00:00
-- url     : https://prove2.me/theorems/0c86bb3d-b10d-4082-9010-45acbe74b291
-- title:
--   Projective probability law supported at zero transports to zero-origin paths
-- statement:
--   The singleton time-zero marginal is supported at zero because each source path starts there. Patch the zero coordinate everywhere, transport the probability to the subtype, and use almost-sure equality of the patched full path to the original full path to preserve every finite marginal.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; reduction of canonicalDensityProjectiveZeroTransferV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalProductZeroOriginMarginalsV1
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (M : NNReal → Measure {path : NNReal → ℝ // path 0 = 0})
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id))) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, IsProbabilityMeasure Q ∧
      ∀ I : Finset NNReal,
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
          Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id)) := by
  sorry
