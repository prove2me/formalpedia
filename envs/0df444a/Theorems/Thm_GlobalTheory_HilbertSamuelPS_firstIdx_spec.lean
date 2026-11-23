-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_spec
-- name    : GlobalTheory.HilbertSamuelPS.firstIdx_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:43.587183+00:00
-- url     : https://prove2.me/theorems/81a3527d-3d69-4e5a-892e-f8371724094a
-- title:
--   Hilbert Samuel PS: first Idx spec
-- statement:
--   The Hilbert Samuel PS construction uses the first Idx spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L124-L129

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

theorem GlobalTheory.HilbertSamuelPS.firstIdx_spec {u : A} (h : ∃ k, evalAt φ k u ≠ 0) :
    evalAt φ (firstIdx φ u) u ≠ 0 ∧ ∀ i < firstIdx φ u, evalAt φ i u = 0 := by sorry
