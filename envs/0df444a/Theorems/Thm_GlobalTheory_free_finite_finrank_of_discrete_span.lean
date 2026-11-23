-- Prove2me | Theorems.Thm_GlobalTheory_free_finite_finrank_of_discrete_span
-- name    : GlobalTheory.free_finite_finrank_of_discrete_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:34.496637+00:00
-- url     : https://prove2.me/theorems/d0369a6e-05e1-403b-abee-8a7dfb6915d5
-- title:
--   Global Theory: free finite finrank of discrete span
-- statement:
--   The Global Theory construction uses the free finite finrank of discrete span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnimodularSymplecticCoordinatesAndLatticeRank.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnimodularSymplecticCoordinatesAndLatticeRank.lean#L24-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by sorry
