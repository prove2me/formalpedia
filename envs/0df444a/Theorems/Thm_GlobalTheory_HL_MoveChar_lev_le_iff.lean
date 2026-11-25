-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveChar_lev_le_iff
-- name    : GlobalTheory.HL.MoveChar.lev_le_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:44.028641+00:00
-- url     : https://prove2.me/theorems/4efa9627-1d08-4025-bde6-b98e5c44d27b
-- title:
--   Move Char: lev le iff
-- statement:
--   The Move Char construction uses the lev le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMoveCharacterNeOne.lean#L51-L62

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

theorem GlobalTheory.HL.MoveChar.lev_le_iff {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by sorry
