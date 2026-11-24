-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_twRel_le_map
-- name    : GlobalTheory.CompanionTheory.CoinvExact.twRel_le_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:19.09808+00:00
-- url     : https://prove2.me/theorems/6dcdbc92-ef5f-4914-bd1f-4cfdbe4996df
-- title:
--   Coinv Exact: tw Rel le map
-- statement:
--   The Coinv Exact construction uses the tw Rel le map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L64-L73

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CoinvExact
variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

theorem GlobalTheory.CompanionTheory.CoinvExact.twRel_le_map (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ).map φ.toLinearMap := by sorry
