-- Prove2me | Theorems.Thm_GlobalTheory_EpsCocycle_eq_one_add_eps
-- name    : GlobalTheory.EpsCocycle.eq_one_add_eps
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:07.788799+00:00
-- url     : https://prove2.me/theorems/053062d3-3574-46e6-a358-1507a30939db
-- title:
--   Eps Cocycle: eq one add eps
-- statement:
--   The Eps Cocycle construction uses the eq one add eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleCocycleOneAddEps.lean#L118-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleCocycleOneAddEps.lean#L118-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section

theorem GlobalTheory.EpsCocycle.eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by sorry
