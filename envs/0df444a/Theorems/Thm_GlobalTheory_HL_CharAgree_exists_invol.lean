-- Prove2me | Theorems.Thm_GlobalTheory_HL_CharAgree_exists_invol
-- name    : GlobalTheory.HL.CharAgree.exists_invol
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:21.288016+00:00
-- url     : https://prove2.me/theorems/24b34b5d-108f-5153-94bb-22f09d71dbc3
-- title:
--   Char Agree: exists invol
-- statement:
--   The Char Agree construction uses the exists invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L12-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L12-L61

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliser
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem GlobalTheory.HL.CharAgree.exists_invol {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → Eˣ),
      (∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum → σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a) ∧
      (∀ a b, a < (bs.map (fun b => (b.2 : ℕ))).sum → b < (bs.map (fun b => (b.2 : ℕ))).sum →
        ptEntryL bs a b = if b = σ a then (t a : E) else 0) ∧
      (∀ c, c + 1 < (bs.map (fun b => (b.2 : ℕ))).sum →
        (σ c = σ (c + 1) + 1 ∧ t (c + 1) = t c) ∨ σ c < σ (c + 1)) := by sorry
