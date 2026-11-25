-- Prove2me | Theorems.Thm_GlobalTheory_T_coinvariants_finite_of_smooth_levi
-- name    : GlobalTheory.T.coinvariants_finite_of_smooth_levi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:56.302846+00:00
-- url     : https://prove2.me/theorems/68a9717e-1feb-45e4-be20-f6215659230b
-- title:
--   T: coinvariants finite of smooth levi
-- statement:
--   The T construction uses the coinvariants finite of smooth levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLeviStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoinvariantsFiniteOfSmoothLeviStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLeviStatement
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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

theorem GlobalTheory.T.coinvariants_finite_of_smooth_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by sorry
