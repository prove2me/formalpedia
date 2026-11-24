-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_eq
-- name    : GlobalTheory.HilbertSamuelPS.firstIdx_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:21.629804+00:00
-- url     : https://prove2.me/theorems/8e9366fa-b26d-47d3-a217-c7e9dc9c2b24
-- title:
--   Hilbert Samuel PS: first Idx eq
-- statement:
--   The Hilbert Samuel PS construction uses the first Idx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L131-L137

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

theorem GlobalTheory.HilbertSamuelPS.firstIdx_eq {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    firstIdx φ u = k := by sorry
