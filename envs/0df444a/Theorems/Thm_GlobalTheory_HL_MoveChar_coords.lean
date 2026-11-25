-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveChar_coords
-- name    : GlobalTheory.HL.MoveChar.coords
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:12:58.291516+00:00
-- url     : https://prove2.me/theorems/4d72246c-a8a1-420d-b8b8-6eb1d85b7fd0
-- title:
--   Move Char: coords
-- statement:
--   The Move Char construction uses the coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L17-L41

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOne
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveChar
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.MoveChar.coords {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by sorry
