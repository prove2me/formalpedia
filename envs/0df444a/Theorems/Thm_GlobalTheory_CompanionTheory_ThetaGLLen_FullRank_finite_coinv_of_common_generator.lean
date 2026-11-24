-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_finite_coinv_of_common_generator
-- name    : GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_of_common_generator
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:51.730167+00:00
-- url     : https://prove2.me/theorems/318491ec-6cbe-47af-b863-0a2c779d844e
-- title:
--   Full Rank: finite coinv of common generator
-- statement:
--   The Full Rank construction uses the finite coinv of common generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean#L8-L48

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

theorem GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_of_common_generator : ∀ (H V : Type) [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (θ : H →* ℂˣ), (∀ w w' : V, ∃ t : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) ∧ w' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t)) → Module.Finite ℂ (V ⧸ twRel ρ θ) := by sorry
