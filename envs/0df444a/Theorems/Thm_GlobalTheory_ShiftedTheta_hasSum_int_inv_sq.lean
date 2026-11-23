-- Prove2me | Theorems.Thm_GlobalTheory_ShiftedTheta_hasSum_int_inv_sq
-- name    : GlobalTheory.ShiftedTheta.hasSum_int_inv_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:43.55408+00:00
-- url     : https://prove2.me/theorems/e034d794-f52d-496e-a80e-98b3638615b2
-- title:
--   Shifted Theta: has Sum int inv sq
-- statement:
--   The Shifted Theta construction uses the has Sum int inv sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta

theorem GlobalTheory.ShiftedTheta.hasSum_int_inv_sq :
    HasSum (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by sorry
