-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_agree_of_isAway
-- name    : GlobalTheory.SqZero.agree_of_isAway
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:32.312312+00:00
-- url     : https://prove2.me/theorems/38774157-2b54-4881-96b4-79c983caed4c
-- title:
--   Sq Zero: agree of is Away
-- statement:
--   The Sq Zero construction uses the agree of is Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L239-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L239-L253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
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
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A : Type} [CommRing A] [Algebra R A]
  {κ : Type} {s : κ → A} {B : κ → Type} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

theorem GlobalTheory.SqZero.agree_of_isAway {B₁ B₂ B₁₂ : Type} [CommRing B₁] [Algebra R B₁] [CommRing B₂] [Algebra R B₂]
    [CommRing B₁₂] [Algebra R B₁₂] {f g : A} {q₁ : A →ₐ[R] B₁} {q₂ : A →ₐ[R] B₂}
    (h₁ : IsAway q₁ f) (h₂ : IsAway q₂ g) {a₀ : B₁ →ₐ[R] B₁₂} {b₀ : B₂ →ₐ[R] B₁₂}
    (e₀ : a₀.comp q₁ = b₀.comp q₂) (h₁₂ : IsAway (a₀.comp q₁) (f * g))
    {y₁ : sp B₁ ⟶ X} {y₂ : sp B₂ ⟶ X} (hy : spMap a₀ ≫ y₁ = spMap b₀ ≫ y₂)
    (T : Type) [CommRing T] [Algebra R T] (a : B₁ →ₐ[R] T) (b : B₂ →ₐ[R] T)
    (e : a.comp q₁ = b.comp q₂) : spMap a ≫ y₁ = spMap b ≫ y₂ := by sorry
