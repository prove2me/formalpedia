-- Prove2me | Theorems.Thm_GlobalTheory_SW_TransComp_qm_sub
-- name    : GlobalTheory.SW.TransComp.qm_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:40.229734+00:00
-- url     : https://prove2.me/theorems/a5333547-80eb-414c-8abf-82a41d90f5d5
-- title:
--   Trans Comp: qm sub
-- statement:
--   The Trans Comp construction uses the qm sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TransComp

theorem GlobalTheory.SW.TransComp.qm_sub {α β : Type} (A B : Matrix α β ℚ) : qm (A - B) = qm A - qm B := by sorry
