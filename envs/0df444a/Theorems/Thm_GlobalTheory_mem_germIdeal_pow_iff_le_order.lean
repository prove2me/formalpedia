-- Prove2me | Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff_le_order
-- name    : GlobalTheory.mem_germIdeal_pow_iff_le_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:30.143233+00:00
-- url     : https://prove2.me/theorems/e856603f-37e0-4f34-afe7-3d8c36180147
-- title:
--   Global Theory: mem germ Ideal pow iff le order
-- statement:
--   The Global Theory construction uses the mem germ Ideal pow iff le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L241-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]

theorem GlobalTheory.mem_germIdeal_pow_iff_le_order [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by sorry
