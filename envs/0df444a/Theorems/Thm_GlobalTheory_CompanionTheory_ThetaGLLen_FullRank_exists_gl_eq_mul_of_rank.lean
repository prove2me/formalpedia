-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_eq_mul_of_rank
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_eq_mul_of_rank
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:46.761798+00:00
-- url     : https://prove2.me/theorems/9b3b79b6-25d4-46c1-8fdc-52eb88f4e64c
-- title:
--   Full Rank: exists gl eq mul of rank
-- statement:
--   The Full Rank construction uses the exists gl eq mul of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L150-L163

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_eq_mul_of_rank : ∀ (k a c : Type) [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (x y : Matrix c a k), x.rank = Fintype.card c → y.rank = Fintype.card c → ∃ g : GL a k, y = x * g.val := by sorry
