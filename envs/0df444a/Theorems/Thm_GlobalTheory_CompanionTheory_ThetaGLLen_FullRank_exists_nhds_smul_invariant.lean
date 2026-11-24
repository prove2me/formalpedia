-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_nhds_smul_invariant
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_nhds_smul_invariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:12.906983+00:00
-- url     : https://prove2.me/theorems/f1953feb-11e4-4803-8086-703a72b649b4
-- title:
--   Full Rank: exists nhds smul invariant
-- statement:
--   The Full Rank construction uses the exists nhds smul invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L50-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L50-L75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_nhds_smul_invariant : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X] (f : SB X), ∃ U ∈ 𝓝 (1 : H), ∀ g ∈ U, ∀ x : X, f.1 (g • x) = f.1 x := by sorry
