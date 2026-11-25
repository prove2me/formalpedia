-- Prove2me | Theorems.Thm_GlobalTheory_apply_eq_genericPoint_of_generalizingMap
-- name    : GlobalTheory.apply_eq_genericPoint_of_generalizingMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:22:16.521674+00:00
-- url     : https://prove2.me/theorems/f5852764-2fac-4e4b-9dcc-a673d516ac4d
-- title:
--   Global Theory: apply eq generic Point of generalizing Map
-- statement:
--   The Global Theory construction uses the apply eq generic Point of generalizing Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L81-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints
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

theorem GlobalTheory.apply_eq_genericPoint_of_generalizingMap {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [T0Space S] [QuasiSober T] [IrreducibleSpace T] {f : S → T}
    (hf : GeneralizingMap f) {s : S} (hs : s ∈ genericPoints S) : f s = genericPoint T := by sorry
