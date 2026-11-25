-- Prove2me | Theorems.Thm_GlobalTheory_etale_of_comp_of_etale_of_surjective
-- name    : GlobalTheory.etale_of_comp_of_etale_of_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:21.288091+00:00
-- url     : https://prove2.me/theorems/936ddc04-f2e3-4c04-8c51-280db9e6632a
-- title:
--   Global Theory: etale of comp of etale of surjective
-- statement:
--   The Global Theory construction uses the etale of comp of etale of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L57-L64

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

theorem GlobalTheory.etale_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by sorry
