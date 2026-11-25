-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDirections_smoothOfRelativeDimension_of_forall_finrank_derivation_le
-- name    : GlobalTheory.SmoothDirections.smoothOfRelativeDimension_of_forall_finrank_derivation_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:24.365264+00:00
-- url     : https://prove2.me/theorems/763e6b7e-fa57-5374-b35e-87e9d211a390
-- title:
--   Smooth Directions: smooth Of Relative Dimension of forall finrank derivation le
-- statement:
--   The Smooth Directions construction uses the smooth Of Relative Dimension of forall finrank derivation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfDirectionsLe.lean#L75-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfDirectionsLe.lean#L75-L101

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

theorem GlobalTheory.SmoothDirections.smoothOfRelativeDimension_of_forall_finrank_derivation_le (k : Type) [Field k]
    [PerfectField k] (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (d : ℕ)
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (ht : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      Module.finrank K (Derivation k R K) ≤ d) :
    SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by sorry
