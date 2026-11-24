-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_row_identity
-- name    : GlobalTheory.CompanionTheory.GapOpLower.row_identity
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:52.407229+00:00
-- url     : https://prove2.me/theorems/9e9d0d83-2af7-44a6-a120-d4428f14856a
-- title:
--   Gap Op Lower: row identity
-- statement:
--   The Gap Op Lower construction uses the row identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L45-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L45-L86

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

theorem GlobalTheory.CompanionTheory.GapOpLower.row_identity {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (N R : (Fin (n + 1) → k) → ℝ) (c : ℝ)
    (hN0 : N 0 = 0)
    (hNa : (Fintype.card k : ℝ) * N a = (Fintype.card k : ℝ) ^ (n + 1))
    (hNs : ∀ s : k, s ≠ 1 → N (s • a) = 0)
    (hNo : ∀ b, (∀ s : k, b ≠ s • a) → (Fintype.card k : ℝ) * N b = (Fintype.card k : ℝ) ^ n)
    (hR : ∀ s : k, s ≠ 0 → R (s • a) = c) :
    (Fintype.card k : ℝ) * ∑ b, N b * R b
      = (Fintype.card k : ℝ) ^ n *
          ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + (Fintype.card k : ℝ) ^ n * c := by sorry
