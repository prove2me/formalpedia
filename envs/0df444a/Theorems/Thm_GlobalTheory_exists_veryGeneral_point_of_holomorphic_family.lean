-- Prove2me | Theorems.Thm_GlobalTheory_exists_veryGeneral_point_of_holomorphic_family
-- name    : GlobalTheory.exists_veryGeneral_point_of_holomorphic_family
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:56.525444+00:00
-- url     : https://prove2.me/theorems/0d877866-c02e-4588-8d39-fd0dc7bf2a55
-- title:
--   Global Theory: exists very General point of holomorphic family
-- statement:
--   The Global Theory construction uses the exists very General point of holomorphic family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsVeryGeneralPointOfHolomorphicFamily.lean#L14-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsVeryGeneralPointOfHolomorphicFamily.lean#L14-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsVeryGeneralPointOfHolomorphicFamily
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

theorem GlobalTheory.exists_veryGeneral_point_of_holomorphic_family :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by sorry
