-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_length_coinvariants_exact
-- name    : GlobalTheory.T.finite_length_coinvariants_exact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:20.13614+00:00
-- url     : https://prove2.me/theorems/eee9fe27-baa9-494f-9da6-48e65b7a7346
-- title:
--   T: finite length coinvariants exact
-- statement:
--   The T construction uses the finite length coinvariants exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExactStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExactStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_length_coinvariants_exact : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by sorry
