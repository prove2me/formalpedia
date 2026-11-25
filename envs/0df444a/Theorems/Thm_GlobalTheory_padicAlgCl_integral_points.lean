-- Prove2me | Theorems.Thm_GlobalTheory_padicAlgCl_integral_points
-- name    : GlobalTheory.padicAlgCl_integral_points
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:57:37.972506+00:00
-- url     : https://prove2.me/theorems/ff31636f-2cbb-5d47-a932-481d7cdacb0e
-- title:
--   Global Theory: padic Alg Cl integral points
-- statement:
--   The Global Theory construction uses the padic Alg Cl integral points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L94-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L94-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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

theorem GlobalTheory.padicAlgCl_integral_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (z : X),
      IsClosed ({z} : Set X) → ∀ U : X.Opens, (U : Set X).Nonempty →
        ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ X),
          y (cPt p) = z ∧ Set.range (gPt p ≫ y) ⊆ U) ∧
    (∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (p : ℕ) [Fact p.Prime]
      (y : Sp (OO p) ⟶ X), ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p),
        FiniteDimensional ℚ_[p] K₀ ∧ ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
          ∃ (j : integralClosure ℤ_[p] K →+* OO p) (y₀ : Sp (integralClosure ℤ_[p] K) ⟶ X),
            (∀ x, ((j x : OO p) : PadicAlgCl p) = ((x : K) : PadicAlgCl p)) ∧ IsLocalHom j ∧
              spMap j ≫ y₀ = y) := by sorry
