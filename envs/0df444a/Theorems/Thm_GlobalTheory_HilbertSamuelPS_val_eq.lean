-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_eq
-- name    : GlobalTheory.HilbertSamuelPS.val_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:30.228809+00:00
-- url     : https://prove2.me/theorems/adfba1d0-e6d7-4b7d-9bb2-5443893b1c24
-- title:
--   Hilbert Samuel PS: val eq
-- statement:
--   The Hilbert Samuel PS construction uses the val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L139-L141

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

theorem GlobalTheory.HilbertSamuelPS.val_eq {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    val φ u = toLex (k, lexOrder (evalAt φ k u)) := by sorry
