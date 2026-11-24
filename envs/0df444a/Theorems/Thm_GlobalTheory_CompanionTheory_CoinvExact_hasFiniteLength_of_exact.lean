-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_hasFiniteLength_of_exact
-- name    : GlobalTheory.CompanionTheory.CoinvExact.hasFiniteLength_of_exact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:12.20529+00:00
-- url     : https://prove2.me/theorems/c7382eef-c554-47ef-8595-bd1e9dcae95c
-- title:
--   Coinv Exact: has Finite Length of exact
-- statement:
--   The Coinv Exact construction uses the has Finite Length of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean#L10-L35

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

theorem GlobalTheory.CompanionTheory.CoinvExact.hasFiniteLength_of_exact {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
    (f : α.IntertwiningMap β) (g : β.IntertwiningMap γ)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength β := by sorry
