-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_liftSemi_prim_baseChange_bijective
-- name    : GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:30.034863+00:00
-- url     : https://prove2.me/theorems/2d2a61c8-38c7-5741-a5f7-4e262f76279c
-- title:
--   PDiv: lift Semi prim base Change bijective
-- statement:
--   The PDiv construction uses the lift Semi prim base Change bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijective.lean#L30-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijective.lean#L30-L55

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.PDiv

theorem GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by sorry
