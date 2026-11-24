-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_level_subset
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_level_subset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:04.011728+00:00
-- url     : https://prove2.me/theorems/87882bf5-1a18-4bb5-8a20-4fab80a8e75e
-- title:
--   Full Rank: exists level subset
-- statement:
--   The Full Rank construction uses the exists level subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L77-L88

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_level_subset : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [TotallyDisconnectedSpace H] (K : Subgroup H), IsCompact (K : Set H) → IsOpen (K : Set H) → ∀ U ∈ 𝓝 (1 : H), ∃ N : Subgroup H, IsOpen (N : Set H) ∧ N ≤ K ∧ (N : Set H) ⊆ U ∧ ∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N := by sorry
