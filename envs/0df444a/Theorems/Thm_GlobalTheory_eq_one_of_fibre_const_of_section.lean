-- Prove2me | Theorems.Thm_GlobalTheory_eq_one_of_fibre_const_of_section
-- name    : GlobalTheory.eq_one_of_fibre_const_of_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:10.35183+00:00
-- url     : https://prove2.me/theorems/109cb1dd-4d84-4d05-96fc-109c974d2ef8
-- title:
--   Global Theory: eq one of fibre const of section
-- statement:
--   The Global Theory construction uses the eq one of fibre const of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfFibreConstOfSection.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfFibreConstOfSection.lean#L14-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfFibreConstOfSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.eq_one_of_fibre_const_of_section :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by sorry
