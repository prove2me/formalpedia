-- Prove2me | Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_isCrys_cyc
-- name    : GlobalTheory.Survey.CrystallineCyclotomic.isCrys_cyc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:47.242798+00:00
-- url     : https://prove2.me/theorems/e039a0c4-1ccc-4cb8-bc13-9e37662bdc15
-- title:
--   Crystalline Cyclotomic: is Crys cyc
-- statement:
--   The Crystalline Cyclotomic construction uses the is Crys cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/CrystallineCyclotomic.lean#L79-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/CrystallineCyclotomic.lean#L79-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.CrystallineCyclotomic
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]

theorem GlobalTheory.Survey.CrystallineCyclotomic.isCrys_cyc [FiniteDimensional Qp LL] : IsCrys PD (charRep (cyc PD LL)) := by sorry
