-- Prove2me | Theorems.Thm_GlobalTheory_HomTrace_finrank_hom
-- name    : GlobalTheory.HomTrace.finrank_hom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:31.580372+00:00
-- url     : https://prove2.me/theorems/3b536ee0-5491-4a45-95c2-650971a98bcf
-- title:
--   Hom Trace: finrank hom
-- statement:
--   The Hom Trace construction uses the finrank hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TraceEqFinrankMulSum.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TraceEqFinrankMulSum.lean#L9-L12

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

theorem GlobalTheory.HomTrace.finrank_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℂ (X →+ ℂ) = Module.finrank ℤ X := by sorry
