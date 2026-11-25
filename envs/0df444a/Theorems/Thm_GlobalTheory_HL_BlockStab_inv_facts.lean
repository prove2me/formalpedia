-- Prove2me | Theorems.Thm_GlobalTheory_HL_BlockStab_inv_facts
-- name    : GlobalTheory.HL.BlockStab.inv_facts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:06.367872+00:00
-- url     : https://prove2.me/theorems/e67e8963-4eba-4400-bb5b-e30cb8e35079
-- title:
--   Block Stab: inv facts
-- statement:
--   The Block Stab construction uses the inv facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L65-L89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
variable {E : Type} [CommRing E] {n : ℕ}

theorem GlobalTheory.HL.BlockStab.inv_facts (A : Matrix (Fin n) (Fin n) E) (hA : IsUni A) :
    ∃ B : Matrix (Fin n) (Fin n) E, A * B = 1 ∧ B * A = 1 ∧ IsUni B ∧
      (∀ O : Subring E, (∀ i j, A i j ∈ O) → ∀ i j, B i j ∈ O) ∧
      ∀ β : Fin n → ℕ, (∀ i j, β i < β j → A i j = 0) → ∀ i j, β i < β j → B i j = 0 := by sorry
