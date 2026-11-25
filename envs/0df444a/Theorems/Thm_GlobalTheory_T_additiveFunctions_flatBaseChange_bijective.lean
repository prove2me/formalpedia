-- Prove2me | Theorems.Thm_GlobalTheory_T_additiveFunctions_flatBaseChange_bijective
-- name    : GlobalTheory.T.additiveFunctions_flatBaseChange_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:58.319643+00:00
-- url     : https://prove2.me/theorems/bc8f0aad-5a8c-45d8-8082-bbe7c3f4358d
-- title:
--   T: additive Functions flat Base Change bijective
-- statement:
--   The T construction uses the additive Functions flat Base Change bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.additiveFunctions_flatBaseChange_bijective : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'], Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by sorry
