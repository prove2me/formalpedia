-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_order_clause_gain
-- name    : KSATSingleFlip.Connect.soft_field_order_clause_gain
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:35:52.787812+00:00
-- url     : https://prove2.me/theorems/fe1889ec-f787-41bd-b13f-674b10410472
-- title:
--   Concave-test order compares the one-clause gain
-- statement:
--   If ν′ precedes ν in the soft-field concave-test order, then their weighted pairings with q ↦ B₍₁₋q₎Ψ(v₀,v₁) are ordered for every continuous concave endpoint-zero test ψ and every nonnegative pair v₀,v₁. This is the sign comparison for a single-clause perturbation in the Poisson interpolation proof of Lemma 4.5; the Poisson derivative and update identity remain separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Mathlib
open MeasureTheory KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_order_clause_gain (ν' ν : Measure ℝ) (hord : softFieldLE ν' ν)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc 0 1)) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    pairing (fun q => softClauseGain ψ v0 v1 (1-q)) ν' ≤
      pairing (fun q => softClauseGain ψ v0 v1 (1-q)) ν := by sorry
