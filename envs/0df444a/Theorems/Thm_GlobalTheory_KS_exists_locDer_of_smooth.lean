-- Prove2me | Theorems.Thm_GlobalTheory_KS_exists_locDer_of_smooth
-- name    : GlobalTheory.KS.exists_locDer_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:36.548547+00:00
-- url     : https://prove2.me/theorems/35e8fdce-891a-4f35-81eb-c01c86dc7496
-- title:
--   KS: exists loc Der of smooth
-- statement:
--   The KS construction uses the exists loc Der of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationAlongFibreOfSmooth.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationAlongFibreOfSmooth.lean#L47-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerivationExtendOfFormallySmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationAlongFibreOfSmooth
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
open GlobalTheory GlobalTheory.KS

theorem GlobalTheory.KS.exists_locDer_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by sorry
