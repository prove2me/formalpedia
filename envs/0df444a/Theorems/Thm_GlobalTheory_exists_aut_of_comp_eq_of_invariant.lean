-- Prove2me | Theorems.Thm_GlobalTheory_exists_aut_of_comp_eq_of_invariant
-- name    : GlobalTheory.exists_aut_of_comp_eq_of_invariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:33.093929+00:00
-- url     : https://prove2.me/theorems/053fcf27-3e5f-4c13-ad65-6687f34a4e6e
-- title:
--   Global Theory: exists aut of comp eq of invariant
-- statement:
--   The Global Theory construction uses the exists aut of comp eq of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulApplyEqOfEqOnInvariants.lean#L71-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulApplyEqOfEqOnInvariants.lean#L71-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
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

theorem GlobalTheory.exists_aut_of_comp_eq_of_invariant {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).hom := by sorry
