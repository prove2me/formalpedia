-- Prove2me | Theorems.Thm_GlobalTheory_algHom_eq_of_reduction_eq_of_coords_eq
-- name    : GlobalTheory.algHom_eq_of_reduction_eq_of_coords_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:13.349491+00:00
-- url     : https://prove2.me/theorems/8a2425c2-d0c3-4ff0-9e2f-983c30fecbb3
-- title:
--   Global Theory: alg Hom eq of reduction eq of coords eq
-- statement:
--   The Global Theory construction uses the alg Hom eq of reduction eq of coords eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AlgHomEqOfReductionEqOfCoordsEq.lean#L9-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AlgHomEqOfReductionEqOfCoordsEq.lean#L9-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgHomEqOfReductionEqOfCoordsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.algHom_eq_of_reduction_eq_of_coords_eq :
    ∀ (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B] (s s' : B →ₐ[O] O) (g : ℕ) (u : Fin g → B), (∀ b, s b - s' b ∈ IsLocalRing.maximalIdeal O) → (∀ i, s (u i) = s' (u i)) → (∀ b, s b = 0 → ∃ t : B, IsUnit (s t) ∧ t * b ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B)) → s = s' := by sorry
