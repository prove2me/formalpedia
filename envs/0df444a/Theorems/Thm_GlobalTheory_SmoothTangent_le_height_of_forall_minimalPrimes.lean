-- Prove2me | Theorems.Thm_GlobalTheory_SmoothTangent_le_height_of_forall_minimalPrimes
-- name    : GlobalTheory.SmoothTangent.le_height_of_forall_minimalPrimes
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:29.723226+00:00
-- url     : https://prove2.me/theorems/9cd22edb-20c1-432e-b497-7ac649ac8e3f
-- title:
--   Smooth Tangent: le height of forall minimal Primes
-- statement:
--   The Smooth Tangent construction uses the le height of forall minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfFinrankDerivatio.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfFinrankDerivatio.lean#L61-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
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
open GlobalTheory GlobalTheory.SmoothTangent

theorem GlobalTheory.SmoothTangent.le_height_of_forall_minimalPrimes (k : Type) [Field k] {R : Type} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (m : Ideal R) [m.IsMaximal] : (d : ℕ∞) ≤ m.height := by sorry
