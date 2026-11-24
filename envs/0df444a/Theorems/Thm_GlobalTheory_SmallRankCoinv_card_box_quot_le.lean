-- Prove2me | Theorems.Thm_GlobalTheory_SmallRankCoinv_card_box_quot_le
-- name    : GlobalTheory.SmallRankCoinv.card_box_quot_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:44.277933+00:00
-- url     : https://prove2.me/theorems/a340b125-cd5d-4135-9685-27c73d6d05dc
-- title:
--   Small Rank Coinv: card box quot le
-- statement:
--   The Small Rank Coinv construction uses the card box quot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L18-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L18-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFullRankSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.SmallRankCoinv
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel GlobalTheory.RankChart GlobalTheory.RankStrata

theorem GlobalTheory.SmallRankCoinv.card_box_quot_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (T R : Type) [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R] {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : kˣ) :
    Nat.card (box T R (ϖ⁻¹ * a) ⧸ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a))) ≤
      GlobalTheory.SplitWeil.resCard k ^ (Fintype.card T * Fintype.card R) := by sorry
