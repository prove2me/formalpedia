-- Prove2me | Theorems.Thm_GlobalTheory_germIdeal_eq_span
-- name    : GlobalTheory.germIdeal_eq_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:08.37506+00:00
-- url     : https://prove2.me/theorems/3b7b8746-30c1-4413-a148-a2025c49e699
-- title:
--   Global Theory: germ Ideal eq span
-- statement:
--   The Global Theory construction uses the germ Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L203-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L203-L212

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

theorem GlobalTheory.germIdeal_eq_span [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by sorry
