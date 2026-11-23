-- Prove2me | Theorems.Thm_GlobalTheory_X_mem_germIdeal
-- name    : GlobalTheory.X_mem_germIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:34.291285+00:00
-- url     : https://prove2.me/theorems/8f3bb555-1f16-4b3b-aae3-3931ba141189
-- title:
--   Global Theory: X mem germ Ideal
-- statement:
--   The Global Theory construction uses the X mem germ Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L164-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L164-L165

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

theorem GlobalTheory.X_mem_germIdeal (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by sorry
