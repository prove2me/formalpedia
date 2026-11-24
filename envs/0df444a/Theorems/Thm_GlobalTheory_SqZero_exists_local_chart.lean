-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_exists_local_chart
-- name    : GlobalTheory.SqZero.exists_local_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:29.515186+00:00
-- url     : https://prove2.me/theorems/7862bb01-aab7-4ebb-b461-da503f0c75ef
-- title:
--   Sq Zero: exists local chart
-- statement:
--   The Sq Zero construction uses the exists local chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L318-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L318-L337

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
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]

theorem GlobalTheory.SqZero.exists_local_chart (y : sp A ⟶ X) (m : Ideal A) (hm : m.IsPrime) :
    ∃ f ∉ m, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (j : sp B ⟶ X),
      IsOpenImmersion j.left ∧ ∀ (T : Type) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T),
        IsUnit (φ f) → ∃ ψ : B →ₐ[R] T, spMap φ ≫ y = spMap ψ ≫ j := by sorry
