-- Prove2me | Theorems.Thm_GlobalTheory_exists_factor_of_lift_fromSpecResidueField
-- name    : GlobalTheory.exists_factor_of_lift_fromSpecResidueField
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:11.283804+00:00
-- url     : https://prove2.me/theorems/127e64b3-817c-5a4f-8d98-805629720ecd
-- title:
--   Global Theory: exists factor of lift from Spec Residue Field
-- statement:
--   The Global Theory construction uses the exists factor of lift from Spec Residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L55-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L55-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory

theorem GlobalTheory.exists_factor_of_lift_fromSpecResidueField {Y W : Scheme.{0}} (h : Y ⟶ W) (w : W)
    (ξ : Spec (W.residueField w) ⟶ Y) (hξ : ξ ≫ h = W.fromSpecResidueField w)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint K) = ξ (IsLocalRing.closedPoint (W.residueField w))) :
    ∃ σ : W.residueField w ⟶ .of K, Spec.map σ ≫ ξ = a := by sorry
