-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_mem_of_coeff_eq_zero
-- name    : GlobalTheory.CompleteBaseChange.mem_of_coeff_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:30.635927+00:00
-- url     : https://prove2.me/theorems/5537cbfa-e161-4623-86eb-b63a0d2160be
-- title:
--   Complete Base Change: mem of coeff eq zero
-- statement:
--   The Complete Base Change construction uses the mem of coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L47-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L47-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange

theorem GlobalTheory.CompleteBaseChange.mem_of_coeff_eq_zero {R σ : Type*} [CommRing R] [Finite σ] (N : ℕ)
    (K : Ideal (MvPowerSeries σ R))
    (hK : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : R) : MvPowerSeries σ R) ∈ K)
    (g : MvPowerSeries σ R) (hg : ∀ d : σ →₀ ℕ, d.degree < N → coeff d g = 0) : g ∈ K := by sorry
