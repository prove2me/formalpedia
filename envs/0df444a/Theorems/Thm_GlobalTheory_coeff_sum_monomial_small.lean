-- Prove2me | Theorems.Thm_GlobalTheory_coeff_sum_monomial_small
-- name    : GlobalTheory.coeff_sum_monomial_small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:09.900158+00:00
-- url     : https://prove2.me/theorems/875f676d-3d8a-405f-90d6-31f80c527a2f
-- title:
--   Global Theory: coeff sum monomial small
-- statement:
--   The Global Theory construction uses the coeff sum monomial small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L28-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory

theorem GlobalTheory.coeff_sum_monomial_small (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by sorry
