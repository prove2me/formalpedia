-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_forall_exists_two_lifts
-- name    : GlobalTheory.exists_ne_zero_forall_exists_two_lifts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:56.929801+00:00
-- url     : https://prove2.me/theorems/778d35d7-42ae-4922-8ac3-4775b0b5450e
-- title:
--   Global Theory: exists ne zero forall exists two lifts
-- statement:
--   The Global Theory construction uses the exists ne zero forall exists two lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L104-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L104-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory

theorem GlobalTheory.exists_ne_zero_forall_exists_two_lifts {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (σ τ : A →ₐ[R] AlgebraicClosure (FractionRing R)) (hne : σ ≠ τ) :
    ∃ r : R, r ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (O : ValuationSubring Ω)
      (φ : R →+* O), φ r ≠ 0 → ∃ ψ ψ' : A →+* O, ψ.comp (algebraMap R A) = φ ∧
        ψ'.comp (algebraMap R A) = φ ∧ ψ ≠ ψ' := by sorry
