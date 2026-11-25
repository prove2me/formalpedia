-- Prove2me | Theorems.Thm_GlobalTheory_WachLettersCompare_isUnit_Q
-- name    : GlobalTheory.WachLettersCompare.isUnit_Q
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:53:33.444073+00:00
-- url     : https://prove2.me/theorems/a67e0eeb-42f4-5d8e-88ab-1865ba9a995e
-- title:
--   Wach Letters Compare: is Unit Q
-- statement:
--   The Wach Letters Compare construction uses the is Unit Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LetterSandwichOfFrobMatrices.lean#L69-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LetterSandwichOfFrobMatrices.lean#L69-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LetterSandwichOfFrobMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.WachLettersCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule

theorem GlobalTheory.WachLettersCompare.isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by sorry
