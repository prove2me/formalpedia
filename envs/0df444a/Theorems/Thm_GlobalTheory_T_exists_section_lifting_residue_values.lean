-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_section_lifting_residue_values
-- name    : GlobalTheory.T.exists_section_lifting_residue_values
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:07.22388+00:00
-- url     : https://prove2.me/theorems/1ff41241-7fd1-4222-a3d8-c3631f143126
-- title:
--   T: exists section lifting residue values
-- statement:
--   The T construction uses the exists section lifting residue values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionLiftingResidueValuesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionLiftingResidueValuesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValuesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_section_lifting_residue_values : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by sorry
