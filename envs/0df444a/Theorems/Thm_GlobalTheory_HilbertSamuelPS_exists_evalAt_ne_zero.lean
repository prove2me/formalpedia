-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_exists_evalAt_ne_zero
-- name    : GlobalTheory.HilbertSamuelPS.exists_evalAt_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:58.112647+00:00
-- url     : https://prove2.me/theorems/863c7478-6ee4-4ba7-bdf1-da9780e17be3
-- title:
--   Hilbert Samuel PS: exists eval At ne zero
-- statement:
--   The Hilbert Samuel PS construction uses the exists eval At ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L145-L149

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

theorem GlobalTheory.HilbertSamuelPS.exists_evalAt_ne_zero (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) {u : A} (hu : u ≠ 0) :
    ∃ k, evalAt φ k u ≠ 0 := by sorry
