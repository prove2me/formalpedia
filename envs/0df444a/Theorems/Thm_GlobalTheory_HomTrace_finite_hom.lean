-- Prove2me | Theorems.Thm_GlobalTheory_HomTrace_finite_hom
-- name    : GlobalTheory.HomTrace.finite_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:58.276842+00:00
-- url     : https://prove2.me/theorems/1670009f-d3e9-48b4-9d80-70839b84e869
-- title:
--   Hom Trace: finite hom
-- statement:
--   The Hom Trace construction uses the finite hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TraceEqFinrankMulSum.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TraceEqFinrankMulSum.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TraceEqFinrankMulSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HomTrace

theorem GlobalTheory.HomTrace.finite_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.Finite ℂ (X →+ ℂ) := by sorry
