-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_liftSemi_toBaseChange_cot_bijective
-- name    : GlobalTheory.PDiv.liftSemi_toBaseChange_cot_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:37.755801+00:00
-- url     : https://prove2.me/theorems/f83690ea-5c77-5979-9c74-79f27568a912
-- title:
--   PDiv: lift Semi to Base Change cot bijective
-- statement:
--   The PDiv construction uses the lift Semi to Base Change cot bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZero.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZero.lean#L8-L32

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory
open GlobalTheory.PDiv

theorem GlobalTheory.PDiv.liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by sorry
