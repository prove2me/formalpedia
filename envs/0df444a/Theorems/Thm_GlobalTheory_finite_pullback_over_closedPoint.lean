-- Prove2me | Theorems.Thm_GlobalTheory_finite_pullback_over_closedPoint
-- name    : GlobalTheory.finite_pullback_over_closedPoint
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:42.452829+00:00
-- url     : https://prove2.me/theorems/71409cd2-d145-44d0-8f19-3a32c2ef10ba
-- title:
--   Global Theory: finite pullback over closed Point
-- statement:
--   The Global Theory construction uses the finite pullback over closed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteOfIsClosedOfFiniteInterClosedPoints.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteOfIsClosedOfFiniteInterClosedPoints.lean#L26-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
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

theorem GlobalTheory.finite_pullback_over_closedPoint {X Z P : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] (s : X ⟶ Z) (t : P ⟶ Z) (σ : X) (hσ : IsClosed ({σ} : Set X))
    {F : Set P} (hF : F.Finite) :
    {w : ↑(pullback s t) | pullback.fst s t w = σ ∧ pullback.snd s t w ∈ F}.Finite := by sorry
