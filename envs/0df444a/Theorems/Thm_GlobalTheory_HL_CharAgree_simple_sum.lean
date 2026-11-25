-- Prove2me | Theorems.Thm_GlobalTheory_HL_CharAgree_simple_sum
-- name    : GlobalTheory.HL.CharAgree.simple_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:11.754601+00:00
-- url     : https://prove2.me/theorems/5efcaba2-9219-4131-a9e7-afa7bd64be55
-- title:
--   Char Agree: simple sum
-- statement:
--   The Char Agree construction uses the simple sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L63-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L63-L141

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

theorem GlobalTheory.HL.CharAgree.simple_sum {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by sorry
