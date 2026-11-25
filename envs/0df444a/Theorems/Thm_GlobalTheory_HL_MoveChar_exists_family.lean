-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveChar_exists_family
-- name    : GlobalTheory.HL.MoveChar.exists_family
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:32.68736+00:00
-- url     : https://prove2.me/theorems/fb5c94d2-0ec4-41f0-a9ca-445ef71a4c34
-- title:
--   Move Char: exists family
-- statement:
--   The Move Char construction uses the exists family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L64-L75

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

theorem GlobalTheory.HL.MoveChar.exists_family {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {J : ℕ} (hJ : J ≤ r + 1) : ∃ y : Fin (J + J) → S.V, LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo g J ⊔ S.spanTo g' J := by sorry
