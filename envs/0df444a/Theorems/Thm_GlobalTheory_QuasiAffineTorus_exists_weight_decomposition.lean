-- Prove2me | Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_weight_decomposition
-- name    : GlobalTheory.QuasiAffineTorus.exists_weight_decomposition
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:58.572993+00:00
-- url     : https://prove2.me/theorems/044744cd-03cd-45e0-8cbc-a9e37d56cb74
-- title:
--   Quasi Affine Torus: exists weight decomposition
-- statement:
--   The Quasi Affine Torus construction uses the exists weight decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L70-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L70-L116

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

theorem GlobalTheory.QuasiAffineTorus.exists_weight_decomposition [Module.Free ℤ X] {U : Type} (j : U → H)
    (hU : ∀ f ∈ A, (∀ u, f (j u) = 0) → f = 0)
    (htr : ∀ f ∈ A, ∀ t, (fun y => f (τ t * y)) ∈ A) {f : H → k} (hf : f ∈ A) (S : Finset X)
    (a : X → U → k)
    (ha : ∀ u t, f (τ t * j u) = ∑ χ ∈ S, (t (Multiplicative.ofAdd χ) : k) * a χ u) :
    ∃ g : S → H → k, (∀ χ, g χ ∈ A ∧
      ∀ t y, g χ (τ t * y) = (t (Multiplicative.ofAdd (χ : X)) : k) * g χ y) ∧ f = ∑ χ, g χ := by sorry
