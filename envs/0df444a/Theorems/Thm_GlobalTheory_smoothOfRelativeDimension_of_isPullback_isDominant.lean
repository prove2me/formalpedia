-- Prove2me | Theorems.Thm_GlobalTheory_smoothOfRelativeDimension_of_isPullback_isDominant
-- name    : GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:32.838717+00:00
-- url     : https://prove2.me/theorems/8633ce0c-656e-5074-9e77-4644e0d998e5
-- title:
--   Global Theory: smooth Of Relative Dimension of is Pullback is Dominant
-- statement:
--   The Global Theory construction uses the smooth Of Relative Dimension of is Pullback is Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfIsPullbackIsDominant.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfIsPullbackIsDominant.lean#L8-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfIsPullbackIsDominant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant :
    ∀ (X U Y Y' : Scheme.{0}) (j : U ⟶ X) (p : Y ⟶ X) (p' : Y' ⟶ U) (φ : Y' ⟶ Y) (g : ℕ),
      IsPullback φ p' p j → IsDominant j → Smooth p → SmoothOfRelativeDimension g p' →
        SmoothOfRelativeDimension g p := by sorry
