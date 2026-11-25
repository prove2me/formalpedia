-- Prove2me | Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_point_of_weights
-- name    : GlobalTheory.QuasiAffineTorus.exists_point_of_weights
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:50.908579+00:00
-- url     : https://prove2.me/theorems/0f1aef62-9ca0-4b62-93f8-b5b8bfed4a65
-- title:
--   Quasi Affine Torus: exists point of weights
-- statement:
--   The Quasi Affine Torus construction uses the exists point of weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L118-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L118-L172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]
variable {H : Type} [CommGroup H] (τ : (Multiplicative X →* kˣ) →* H) (A : Subalgebra k (H → k))

theorem GlobalTheory.QuasiAffineTorus.exists_point_of_weights (hdom : ∀ f ∈ A, ∀ g ∈ A, f * g = 0 → f = 0 ∨ g = 0)
    (hinv : ∀ f ∈ A, (fun y => f y⁻¹) ∈ A)
    (hc : ∀ f ∈ A, (∀ t y, f (τ t * y) = f y) → ∀ y, f y = f 1) (x : H) :
    ∃ t, ∀ g ∈ A, ∀ χ : X, (∀ t y, g (τ t * y) = (t (Multiplicative.ofAdd χ) : k) * g y) →
      g x = g (τ t) := by sorry
