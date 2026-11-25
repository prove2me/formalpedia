-- Prove2me | Theorems.Thm_GlobalTheory_TorusTransfer_exists_siegel_coordinates
-- name    : GlobalTheory.TorusTransfer.exists_siegel_coordinates
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:49:34.087342+00:00
-- url     : https://prove2.me/theorems/ce124ea4-862d-4111-9281-75a46c5bfaf8
-- title:
--   Torus Transfer: exists siegel coordinates
-- statement:
--   The Torus Transfer construction uses the exists siegel coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqZeroOfFderivEqZero.lean#L149-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqZeroOfFderivEqZero.lean#L149-L247

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorusTransfer
open SiegelNormalForm
variable {g : ℕ}

theorem GlobalTheory.TorusTransfer.exists_siegel_coordinates (Λ : Submodule ℤ (Fin g → ℂ)) (hdisc : DiscreteTopology Λ)
    (hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℝ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      (Y.map (↑) : Matrix _ _ ℂ).IsSymm ∧ Y * τ.map Complex.im = 1 ∧
      ∀ z w, φ z ⬝ᵥ Hm *ᵥ star (φ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w := by sorry
