-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_formallyUnramified_of_comp_faithfullyFlat
-- name    : GlobalTheory.ringHom_formallyUnramified_of_comp_faithfullyFlat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:45.470594+00:00
-- url     : https://prove2.me/theorems/5099a544-b670-4309-97ec-8c450a3e24cf
-- title:
--   Global Theory: ring Hom formally Unramified of comp faithfully Flat
-- statement:
--   The Global Theory construction uses the ring Hom formally Unramified of comp faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FormallyUnramifiedOfCompOfEtaleOfSurjective.lean#L17-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

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
open TensorProduct

theorem GlobalTheory.ringHom_formallyUnramified_of_comp_faithfullyFlat {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by sorry
