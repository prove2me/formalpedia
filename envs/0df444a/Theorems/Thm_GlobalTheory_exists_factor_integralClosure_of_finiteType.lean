-- Prove2me | Theorems.Thm_GlobalTheory_exists_factor_integralClosure_of_finiteType
-- name    : GlobalTheory.exists_factor_integralClosure_of_finiteType
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:45:51.040724+00:00
-- url     : https://prove2.me/theorems/2724838f-060a-4d87-92ad-424835a8dd82
-- title:
--   Global Theory: exists factor integral Closure of finite Type
-- statement:
--   The Global Theory construction uses the exists factor integral Closure of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L51-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L51-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
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
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.exists_factor_integralClosure_of_finiteType {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (φ : A →+* OO p) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
        ∃ ψ : A →+* integralClosure ℤ_[p] K,
          (integralClosureToPadicAlgClIntegers K).comp ψ = φ := by sorry
