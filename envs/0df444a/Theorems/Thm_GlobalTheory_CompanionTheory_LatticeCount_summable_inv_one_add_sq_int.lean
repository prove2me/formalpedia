-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_inv_one_add_sq_int
-- name    : GlobalTheory.CompanionTheory.LatticeCount.summable_inv_one_add_sq_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:53.763795+00:00
-- url     : https://prove2.me/theorems/65011b05-6055-43d8-a88f-dfe9a792e19b
-- title:
--   Lattice Count: summable inv one add sq int
-- statement:
--   The Lattice Count construction uses the summable inv one add sq int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L6-L23

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

theorem GlobalTheory.CompanionTheory.LatticeCount.summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by sorry
