-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_indicator_orb
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_indicator_orb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:54.713802+00:00
-- url     : https://prove2.me/theorems/d50a6fb3-c95e-4f67-b15b-71406bb910b3
-- title:
--   Full Rank: exists indicator orb
-- statement:
--   The Full Rank construction uses the exists indicator orb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L203-L209

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
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_indicator_orb [T2Space X] [ContinuousSMul H X] (hopen : ∀ x : X, IsOpenMap fun g : H => g • x)
    {K N : Subgroup H} (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (x₀ : X) :
    ∃ v : SB X, ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x := by sorry
