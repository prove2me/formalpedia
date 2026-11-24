-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_mul
-- name    : GlobalTheory.HilbertSamuelPS.evalAt_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:21:27.94727+00:00
-- url     : https://prove2.me/theorems/03e07a0b-8fdb-45b5-a75e-a8bbfa372bf9
-- title:
--   Hilbert Samuel PS: eval At mul
-- statement:
--   The Hilbert Samuel PS construction uses the eval At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L112-L113

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

theorem GlobalTheory.HilbertSamuelPS.evalAt_mul (k : ℕ) (u v : A) : evalAt φ k (u * v) = evalAt φ k u * evalAt φ k v := by sorry
