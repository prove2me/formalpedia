-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_coinvMap_mk
-- name    : GlobalTheory.CompanionTheory.CoinvExact.coinvMap_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:34.022948+00:00
-- url     : https://prove2.me/theorems/4af3400a-a69f-4f83-bc93-0d19f3406ec9
-- title:
--   Coinv Exact: coinv Map mk
-- statement:
--   The Coinv Exact construction uses the coinv Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L61-L62

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
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

theorem GlobalTheory.CompanionTheory.CoinvExact.coinvMap_mk (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := by sorry
