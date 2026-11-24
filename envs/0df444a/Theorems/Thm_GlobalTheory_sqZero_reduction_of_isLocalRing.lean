-- Prove2me | Theorems.Thm_GlobalTheory_sqZero_reduction_of_isLocalRing
-- name    : GlobalTheory.sqZero_reduction_of_isLocalRing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:26.679033+00:00
-- url     : https://prove2.me/theorems/ff8af570-484e-4f26-8058-7e55754f3909
-- title:
--   Global Theory: sq Zero reduction of is Local Ring
-- statement:
--   The Global Theory construction uses the sq Zero reduction of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L468-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean#L468-L477

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory
open SqZero
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.sqZero_reduction_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R))
    [GrpObj G] [IsCommMonObj G] [Smooth G.hom] :
    ∃ n : ℕ, ∀ (A : Type) [CommRing A] [Algebra R A] (J : Ideal A), J ^ 2 = ⊥ →
      Nonempty (Additive (redKer (R := R) G J) ≃+ (Fin n → J)) ∧
      (∀ y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G, ∃ y : sp A ⟶ G, spMap (Ideal.Quotient.mkₐ R J) ≫ y = y₀) ∧
      ∀ k : ℕ, (∀ a ∈ J, k • a = 0) → ∀ y ∈ redKer (R := R) G J, y ^ k = 1 := by sorry
