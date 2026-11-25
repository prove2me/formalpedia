-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_exists_frames_term
-- name    : GlobalTheory.HL.Inhab.exists_frames_term
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:36.46433+00:00
-- url     : https://prove2.me/theorems/528d6853-4d6c-4b73-9f82-161f8568042f
-- title:
--   Inhab: exists frames term
-- statement:
--   The Inhab construction uses the exists frames term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L616-L626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L616-L626

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

theorem GlobalTheory.HL.Inhab.exists_frames_term (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (∃ S : Frames L 1 (m + 1), S.ϖ = ϖ ∧ S.w.blocks = [(1, 2)] ∧ S.T = 1 ∧ S.T' = 1 ∧ S.gg = false ∧
      S.G = 1 ∧ S.a = 0 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) ∧
    (¬ IsField E → ∃ S : Frames L 1 (m + 3), S.ϖ = ϖ ∧ S.gg = true ∧
      S.G = algebraMap F E ((ϖ : F) ^ 6) ∧ S.a = 2 ∧ ∃ d Λ, S.IsTerm d Λ ∧ IsSD L S.Hm Λ) := by sorry
