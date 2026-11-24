-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_mul_eq_base
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_mul_eq_base
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:22.869647+00:00
-- url     : https://prove2.me/theorems/25fa4b44-e488-46d5-b055-ca37524ef85e
-- title:
--   Full Rank: exists gl mul eq base
-- statement:
--   The Full Rank construction uses the exists gl mul eq base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L125-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L125-L146

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
variable {k a c d : Type} [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_mul_eq_base (e : c ⊕ d ≃ a) (x : Matrix c a k) (hx : x.rank = Fintype.card c) :
    ∃ g : GL a k, ∀ i s, (x * g.val) i (e s) = Sum.elim (fun j => (1 : Matrix c c k) i j) (fun _ => 0) s := by sorry
