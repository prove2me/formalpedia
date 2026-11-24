-- Prove2me | Theorems.Thm_GlobalTheory_QuotientGluing_exists_of_charts
-- name    : GlobalTheory.QuotientGluing.exists_of_charts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:22.375902+00:00
-- url     : https://prove2.me/theorems/64bbaf7b-f641-41cd-a080-2ac8605b3a29
-- title:
--   Quotient Gluing: exists of charts
-- statement:
--   The Quotient Gluing construction uses the exists of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L70-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L70-L201

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QuotientGluing.exists_of_charts (ρ : G →* Aut X) (𝒰 : Set X.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U : 𝒰, x ∈ U.1)
    (T : 𝒰 → Scheme.{0}) (i : ∀ U, T U ⟶ X) [∀ U, IsOpenImmersion (i U)]
    (hr : ∀ U, (i U).opensRange = U.1) (haff : ∀ U : 𝒰, IsAffineOpen U.1)
    (σ : ∀ U, G →* Aut (T U)) (hσ : ∀ U g, (σ U g).hom ≫ i U = i U ≫ (ρ g).hom)
    (Y : 𝒰 → Scheme.{0}) [∀ U, IsAffine (Y U)] (q : ∀ U, T U ⟶ Y U)
    (hq : ∀ U, IsAffineQuotient (σ U) (q U)) :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by sorry
