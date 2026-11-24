-- Prove2me | Theorems.Thm_GlobalTheory_QuotientGluing_app_of_chart
-- name    : GlobalTheory.QuotientGluing.app_of_chart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:12.647266+00:00
-- url     : https://prove2.me/theorems/230a2533-eab4-4450-b9c7-c048aa0a224e
-- title:
--   Quotient Gluing: app of chart
-- statement:
--   The Quotient Gluing construction uses the app of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L41-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L41-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}
omit [Finite G]

theorem GlobalTheory.QuotientGluing.app_of_chart {T Y Y' : Scheme.{0}} {ρ : G →* Aut X} {σ : G →* Aut T}
    {q : T ⟶ Y'} (h : IsAffineQuotient σ q) (π : X ⟶ Y) (i : T ⟶ X) [IsOpenImmersion i]
    (hi : ∀ g, (σ g).hom ≫ i = i ≫ (ρ g).hom) (κ : Y' ⟶ Y) [IsOpenImmersion κ]
    (hκ : i ≫ π = q ≫ κ) (W : Y.Opens) (hW : W ≤ κ.opensRange) (hW' : π ⁻¹ᵁ W ≤ i.opensRange) :
    Function.Injective (π.app W) ∧
      ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by sorry
