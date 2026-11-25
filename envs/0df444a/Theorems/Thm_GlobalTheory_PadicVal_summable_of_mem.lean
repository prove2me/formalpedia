-- Prove2me | Theorems.Thm_GlobalTheory_PadicVal_summable_of_mem
-- name    : GlobalTheory.PadicVal.summable_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:24.524793+00:00
-- url     : https://prove2.me/theorems/a8425c1d-0a36-4b12-a50d-36be5bb56674
-- title:
--   Padic Val: summable of mem
-- statement:
--   The Padic Val construction uses the summable of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuation.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuation.lean#L124-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.PadicVal.summable_of_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {I : Type} {x : I → PadicAlgCl p} (hK : ∀ i, x i ∈ K) (hx : Filter.Tendsto x Filter.cofinite (nhds 0)) :
    Summable x := by sorry
