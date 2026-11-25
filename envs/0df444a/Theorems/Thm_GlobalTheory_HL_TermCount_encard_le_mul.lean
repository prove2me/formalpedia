-- Prove2me | Theorems.Thm_GlobalTheory_HL_TermCount_encard_le_mul
-- name    : GlobalTheory.HL.TermCount.encard_le_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:35:40.943329+00:00
-- url     : https://prove2.me/theorems/1590365e-1cae-441b-9f21-4001bc65e11c
-- title:
--   Term Count: encard le mul
-- statement:
--   The Term Count construction uses the encard le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianTermCountFrameClassLe.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianTermCountFrameClassLe.lean#L17-L34

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermCountFrameClassLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TermCount

theorem GlobalTheory.HL.TermCount.encard_le_mul {α β : Type} (s : Set α) (f : α → β) (t : Set β) (A B : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : (t.encard : ℝ≥0∞) ≤ A)
    (hB : ∀ b ∈ t, (({a | a ∈ s ∧ f a = b} : Set α).encard : ℝ≥0∞) ≤ B) :
    (s.encard : ℝ≥0∞) ≤ A * B := by sorry
