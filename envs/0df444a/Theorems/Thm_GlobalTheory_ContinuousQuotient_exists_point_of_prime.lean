-- Prove2me | Theorems.Thm_GlobalTheory_ContinuousQuotient_exists_point_of_prime
-- name    : GlobalTheory.ContinuousQuotient.exists_point_of_prime
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:58:56.029704+00:00
-- url     : https://prove2.me/theorems/956cf9af-d419-4d37-9564-b0ff64f47508
-- title:
--   Continuous Quotient: exists point of prime
-- statement:
--   The Continuous Quotient construction uses the exists point of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEqMulOfContinuousOnQuotient.lean#L162-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEqMulOfContinuousOnQuotient.lean#L162-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient
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
open scoped CategoryTheory.Obj TensorProduct Topology
open GlobalTheory GlobalTheory.ContinuousQuotient

theorem GlobalTheory.ContinuousQuotient.exists_point_of_prime (X : Over (Sp ℂ)) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) (p : Ideal Γ(X.left, U)) [p.IsPrime] {s : Γ(X.left, U)} (hs : s ∉ p) :
    ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U s ≠ 0 ∧
      ∀ r ∈ p, valAt' x.left U r = 0 := by sorry
