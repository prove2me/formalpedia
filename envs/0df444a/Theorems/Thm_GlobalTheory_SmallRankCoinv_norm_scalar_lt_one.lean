-- Prove2me | Theorems.Thm_GlobalTheory_SmallRankCoinv_norm_scalar_lt_one
-- name    : GlobalTheory.SmallRankCoinv.norm_scalar_lt_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:25.410941+00:00
-- url     : https://prove2.me/theorems/35983e6c-bca9-4f2d-9a81-87d85552a98a
-- title:
--   Small Rank Coinv: norm scalar lt one
-- statement:
--   The Small Rank Coinv construction uses the norm scalar lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L58-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L58-L80

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

theorem GlobalTheory.SmallRankCoinv.norm_scalar_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {z : ℂ} (hz : ‖z‖ = 1) {t r d c : ℕ} (ht : 0 < t) (hrd : 2 * r < d)
    (hc : c ≤ GlobalTheory.SplitWeil.resCard k ^ (t * r)) : ‖z ^ t * apow (ϖ ^ t) ((d : ℂ) / 2) * (c : ℂ)‖ < 1 := by sorry
