-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_omega_baseChange_bijective
-- name    : GlobalTheory.PDivGroup.omega_baseChange_bijective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:02:05.221657+00:00
-- url     : https://prove2.me/theorems/c2016a42-7216-4bf8-94dc-46ab38104802
-- title:
--   PDiv Group: omega base Change bijective
-- statement:
--   The PDiv Group construction uses the omega base Change bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZero.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmegaBaseChangeBijectiveOfPEqZero.lean#L38-L58

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
open GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by sorry
