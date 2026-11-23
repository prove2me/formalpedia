-- Prove2me | Theorems.Thm_GlobalTheory_faithfullyFlat_stalkMap_of_flat
-- name    : GlobalTheory.faithfullyFlat_stalkMap_of_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:30.09539+00:00
-- url     : https://prove2.me/theorems/71c956b3-f9dc-40c2-bf2a-ad00a2ee9071
-- title:
--   Global Theory: faithfully Flat stalk Map of flat
-- statement:
--   The Global Theory construction uses the faithfully Flat stalk Map of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L28-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
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
universe u

theorem GlobalTheory.faithfullyFlat_stalkMap_of_flat {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by sorry
