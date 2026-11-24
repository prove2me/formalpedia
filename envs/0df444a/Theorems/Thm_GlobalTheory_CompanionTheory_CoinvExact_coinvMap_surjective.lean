-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_coinvMap_surjective
-- name    : GlobalTheory.CompanionTheory.CoinvExact.coinvMap_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:42:24.69579+00:00
-- url     : https://prove2.me/theorems/e9481780-eaea-4c54-91ba-6be96d473e50
-- title:
--   Coinv Exact: coinv Map surjective
-- statement:
--   The Coinv Exact construction uses the coinv Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L75-L80

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

theorem GlobalTheory.CompanionTheory.CoinvExact.coinvMap_surjective (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    Function.Surjective (coinvMap φ ψ) := by sorry
