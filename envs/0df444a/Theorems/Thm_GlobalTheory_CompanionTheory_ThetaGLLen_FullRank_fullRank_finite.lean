-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_fullRank_finite
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.fullRank_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:53.957677+00:00
-- url     : https://prove2.me/theorems/822a1a8c-5cbe-44d7-b9c0-c609c7bde55d
-- title:
--   Full Rank: full Rank finite
-- statement:
--   The Full Rank construction uses the full Rank finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L420-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L420-L454

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.fullRank_finite (κ : ℕ) (hκ : κ = Fintype.card c) (θ : GL a k →* ℂˣ) :
    Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by sorry
