-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_sub
-- name    : GlobalTheory.HilbertSamuelPS.evalAt_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:32.613942+00:00
-- url     : https://prove2.me/theorems/70e96778-feb1-4e8c-b3cc-e28051eafab5
-- title:
--   Hilbert Samuel PS: eval At sub
-- statement:
--   The Hilbert Samuel PS construction uses the eval At sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L108-L109

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

theorem GlobalTheory.HilbertSamuelPS.evalAt_sub (k : ℕ) (u v : A) : evalAt φ k (u - v) = evalAt φ k u - evalAt φ k v := by sorry
