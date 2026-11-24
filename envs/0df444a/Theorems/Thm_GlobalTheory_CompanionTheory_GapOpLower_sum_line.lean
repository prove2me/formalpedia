-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_sum_line
-- name    : GlobalTheory.CompanionTheory.GapOpLower.sum_line
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:45.111898+00:00
-- url     : https://prove2.me/theorems/fa28621b-3508-45b4-ad0b-dbcfab289096
-- title:
--   Gap Op Lower: sum line
-- statement:
--   The Gap Op Lower construction uses the sum line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCountFromHyperplanes.lean#L24-L43

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

theorem GlobalTheory.CompanionTheory.GapOpLower.sum_line {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (D : (Fin (n + 1) → k) → ℝ) (hD : ∀ b, (∀ s : k, b ≠ s • a) → D b = 0) :
    ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), D b
      = ∑ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), D (s • a) := by sorry
