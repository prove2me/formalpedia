-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodClass_unit_of_lead
-- name    : GlobalTheory.HL.GoodClass.unit_of_lead
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:32:25.690703+00:00
-- url     : https://prove2.me/theorems/6ff4f0f0-51b7-57c8-9d6b-bc670e2d6100
-- title:
--   Good Class: unit of lead
-- statement:
--   The Good Class construction uses the unit of lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L251-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitEntries.lean#L251-L302

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem GlobalTheory.HL.GoodClass.unit_of_lead [Nontrivial E] (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O)
    {n : ℕ} (w : Pt E n) (ε : Fin n → ℕ) (Z : Matrix (Fin n) (Fin n) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ ε b) (h : ∀ l, lead Z l ≠ 0 → UnitIn O (lead Z l)) :
    ∃ σ : Fin n → Fin n, (∀ a, σ (σ a) = a) ∧ (∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b) ∧
      (∀ a b, b ≠ σ a → Z a b = 0) ∧ ∀ a, UnitIn O (Z a (σ a)) := by sorry
