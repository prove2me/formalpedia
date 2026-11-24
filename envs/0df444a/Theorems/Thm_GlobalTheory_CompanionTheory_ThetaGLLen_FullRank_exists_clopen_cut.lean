-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_clopen_cut
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_clopen_cut
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:57.371164+00:00
-- url     : https://prove2.me/theorems/e5192baf-6787-46bc-af9f-509e501037a8
-- title:
--   Full Rank: exists clopen cut
-- statement:
--   The Full Rank construction uses the exists clopen cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L104-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L104-L119

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_clopen_cut : ∀ (X : Type) [TopologicalSpace X] (Y : Set X), IsClopen Y → ∀ f : SB X, ∃ f₁ f₂ : SB X, f = f₁ + f₂ ∧ (∀ x, f₁.1 x ≠ 0 → x ∈ Y ∧ f.1 x ≠ 0) ∧ (∀ x, f₂.1 x ≠ 0 → x ∉ Y ∧ f.1 x ≠ 0) := by sorry
