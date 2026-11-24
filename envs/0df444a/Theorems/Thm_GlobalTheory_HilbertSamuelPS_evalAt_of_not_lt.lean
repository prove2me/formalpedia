-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_of_not_lt
-- name    : GlobalTheory.HilbertSamuelPS.evalAt_of_not_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:21:49.665135+00:00
-- url     : https://prove2.me/theorems/f4507dce-d4cd-4eab-886d-7aa4a20ca6f8
-- title:
--   Hilbert Samuel PS: eval At of not lt
-- statement:
--   The Hilbert Samuel PS construction uses the eval At of not lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L102-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))

theorem GlobalTheory.HilbertSamuelPS.evalAt_of_not_lt {k : ℕ} (h : ¬ k < n) (u : A) : evalAt φ k u = 0 := by sorry
