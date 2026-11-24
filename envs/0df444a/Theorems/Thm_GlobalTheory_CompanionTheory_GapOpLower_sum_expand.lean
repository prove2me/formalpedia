-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_sum_expand
-- name    : GlobalTheory.CompanionTheory.GapOpLower.sum_expand
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:46.510209+00:00
-- url     : https://prove2.me/theorems/867244f2-bc86-425b-a91d-145616b71c2f
-- title:
--   Gap Op Lower: sum expand
-- statement:
--   The Gap Op Lower construction uses the sum expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L88-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L88-L111

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset

theorem GlobalTheory.CompanionTheory.GapOpLower.sum_expand {k : Type} [Field k] [Fintype k] {n : ℕ}
    (R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ) :
    ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ a, ∑ b, ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
          * R a b := by sorry
