-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_prod_inv_one_add_sq
-- name    : GlobalTheory.CompanionTheory.LatticeCount.summable_prod_inv_one_add_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:58.633431+00:00
-- url     : https://prove2.me/theorems/a5019598-1751-40ea-9724-7f002eb24322
-- title:
--   Lattice Count: summable prod inv one add sq
-- statement:
--   The Lattice Count construction uses the summable prod inv one add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L25-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticeCount

theorem GlobalTheory.CompanionTheory.LatticeCount.summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by sorry
