-- Prove2me | Theorems.Thm_GlobalTheory_exists_factor_of_isLocalRing_of_mem_affineOpen
-- name    : GlobalTheory.exists_factor_of_isLocalRing_of_mem_affineOpen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:07:27.69458+00:00
-- url     : https://prove2.me/theorems/f81cedf7-e812-481a-a742-69efe7904725
-- title:
--   Global Theory: exists factor of is Local Ring of mem affine Open
-- statement:
--   The Global Theory construction uses the exists factor of is Local Ring of mem affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L148-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
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

theorem GlobalTheory.exists_factor_of_isLocalRing_of_mem_affineOpen {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hz : y (IsLocalRing.closedPoint R) ∈ V) :
    ∃ φ : Γ(X, V) ⟶ R, Spec.map φ ≫ hV.fromSpec = y := by sorry
