-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_lTensor_transl_comul
-- name    : GlobalTheory.PDivGroup.lTensor_transl_comul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:50:05.618615+00:00
-- url     : https://prove2.me/theorems/320ec7b8-45ac-494f-ab32-aa3ce8f19832
-- title:
--   PDiv Group: l Tensor transl comul
-- statement:
--   The PDiv Group construction uses the l Tensor transl comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoboundaryTranslationInvariantPTorsion.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoboundaryTranslationInvariantPTorsion.lean#L14-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoboundaryTranslationInvariantPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem GlobalTheory.PDivGroup.lTensor_transl_comul (n : ℕ) (x : G.A (n + 1)) :
    (G.transl n).toLinearMap.lTensor (G.A (n + 1)) (comul (R := R) x) =
      TensorProduct.assoc R _ _ _ ((comul (R := R)).rTensor (G.A 1) (G.transl n x)) := by sorry
