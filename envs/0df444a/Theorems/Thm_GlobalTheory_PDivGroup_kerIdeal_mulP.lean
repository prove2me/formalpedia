-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_kerIdeal_mulP
-- name    : GlobalTheory.PDivGroup.kerIdeal_mulP
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:02:28.486892+00:00
-- url     : https://prove2.me/theorems/02db6cc7-fcc6-411f-9dcf-49a2d85657da
-- title:
--   PDiv Group: ker Ideal mul P
-- statement:
--   The PDiv Group construction uses the ker Ideal mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L73-L78

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
open scoped TensorProduct
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)

theorem GlobalTheory.PDivGroup.kerIdeal_mulP (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by sorry
