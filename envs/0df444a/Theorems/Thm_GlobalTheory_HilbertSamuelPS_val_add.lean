-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_add
-- name    : GlobalTheory.HilbertSamuelPS.val_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:15.512718+00:00
-- url     : https://prove2.me/theorems/644d212f-71d3-4f43-9e81-e519b6cd7d26
-- title:
--   Hilbert Samuel PS: val add
-- statement:
--   The Hilbert Samuel PS construction uses the val add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L164-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L164-L187

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
variable {φ}

theorem GlobalTheory.HilbertSamuelPS.val_add (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0)
    (hlt : val φ u < val φ v) : u + v ≠ 0 ∧ val φ (u + v) = val φ u := by sorry
