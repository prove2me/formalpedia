-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDirections_finrank_derivation_le
-- name    : GlobalTheory.SmoothDirections.finrank_derivation_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:07:06.586132+00:00
-- url     : https://prove2.me/theorems/179aa9fd-e473-4233-9eea-b56520f48a3d
-- title:
--   Smooth Directions: finrank derivation le
-- statement:
--   The Smooth Directions construction uses the finrank derivation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfDirectionsLe.lean#L37-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfDirectionsLe.lean#L37-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe
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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDirections

theorem GlobalTheory.SmoothDirections.finrank_derivation_le {k R K : Type} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {X : Scheme.{0}}
    (s : X ⟶ Sp k) (j : Sp R ⟶ X) [Mono j] (hj : j ≫ s = spMap (algebraMap k R)) {d : ℕ}
    (ht : ∀ (r : ℕ) (β : k →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
      x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
      (∀ lam : (Fin r → K) →ₗ[K] K,
        spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) :
    Module.finrank K (Derivation k R K) ≤ d := by sorry
