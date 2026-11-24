-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_indicator_mem_SB_of_isClopen
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.indicator_mem_SB_of_isClopen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:15.899795+00:00
-- url     : https://prove2.me/theorems/a198a153-f2a0-40da-ad5f-a4124940e1fb
-- title:
--   Full Rank: indicator mem SB of is Clopen
-- statement:
--   The Full Rank construction uses the indicator mem SB of is Clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L90-L102

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.indicator_mem_SB_of_isClopen {X : Type} [TopologicalSpace X] {Y : Set X} (hY : IsClopen Y) (f : SB X) :
    Y.indicator f.1 ∈ SB X := by sorry
