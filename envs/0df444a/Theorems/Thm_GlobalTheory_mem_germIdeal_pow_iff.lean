-- Prove2me | Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
-- name    : GlobalTheory.mem_germIdeal_pow_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:48.426904+00:00
-- url     : https://prove2.me/theorems/8b8278c4-bd31-4aed-b755-d8af8333de38
-- title:
--   Global Theory: mem germ Ideal pow iff
-- statement:
--   The Global Theory construction uses the mem germ Ideal pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L214-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L214-L239

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

theorem GlobalTheory.mem_germIdeal_pow_iff [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by sorry
