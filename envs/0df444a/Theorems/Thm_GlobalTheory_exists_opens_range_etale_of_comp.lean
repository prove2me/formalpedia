-- Prove2me | Theorems.Thm_GlobalTheory_exists_opens_range_etale_of_comp
-- name    : GlobalTheory.exists_opens_range_etale_of_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:18.999102+00:00
-- url     : https://prove2.me/theorems/5a0dac60-74df-46a6-ad64-18652ea6ae09
-- title:
--   Global Theory: exists opens range etale of comp
-- statement:
--   The Global Theory construction uses the exists opens range etale of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L66-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L66-L86

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

theorem GlobalTheory.exists_opens_range_etale_of_comp :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by sorry
