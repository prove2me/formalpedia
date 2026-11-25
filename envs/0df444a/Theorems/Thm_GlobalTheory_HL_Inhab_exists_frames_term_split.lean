-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_exists_frames_term_split
-- name    : GlobalTheory.HL.Inhab.exists_frames_term_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:35.16903+00:00
-- url     : https://prove2.me/theorems/c7e81784-b2c9-53e2-a31a-0154eecd651d
-- title:
--   Inhab: exists frames term split
-- statement:
--   The Inhab construction uses the exists frames term split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L628-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L628-L641

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Inhab.exists_frames_term_split [IsNonarchimedeanLocalField F] (m : ℕ) :
    ∃ L : LocE F (F × F),
      (∃ S : Frames L 1 (m + 1), S.gg = false ∧ ∃ d Λ, S.IsTerm d Λ) ∧
      ∃ S : Frames L 1 (m + 3), S.gg = true ∧ ∃ d Λ, S.IsTerm d Λ := by sorry
