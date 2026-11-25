-- Prove2me | Theorems.Thm_GlobalTheory_integralFamily_at_prime
-- name    : GlobalTheory.integralFamily_at_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:52.1898+00:00
-- url     : https://prove2.me/theorems/50f8c2e7-33df-4c0e-8764-7532e6bc9b3b
-- title:
--   Global Theory: integral Family at prime
-- statement:
--   The Global Theory construction uses the integral Family at prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L363-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L363-L424

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open FamIntAt SectionScalarValuation

theorem GlobalTheory.integralFamily_at_prime : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by sorry
