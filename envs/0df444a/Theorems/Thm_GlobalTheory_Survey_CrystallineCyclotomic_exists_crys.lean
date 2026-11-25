-- Prove2me | Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_exists_crys
-- name    : GlobalTheory.Survey.CrystallineCyclotomic.exists_crys
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:49.116575+00:00
-- url     : https://prove2.me/theorems/e08a9f20-94a6-4ed8-96cd-2b004315f64e
-- title:
--   Crystalline Cyclotomic: exists crys
-- statement:
--   The Crystalline Cyclotomic construction uses the exists crys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/CrystallineCyclotomic.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/CrystallineCyclotomic.lean#L104-L107

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

theorem GlobalTheory.Survey.CrystallineCyclotomic.exists_crys (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    IsCrys (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) := by sorry
