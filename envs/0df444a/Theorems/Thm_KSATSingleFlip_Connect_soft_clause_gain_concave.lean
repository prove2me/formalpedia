-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_clause_gain_concave
-- name    : KSATSingleFlip.Connect.soft_clause_gain_concave
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:32:30.273231+00:00
-- url     : https://prove2.me/theorems/008e6f5b-f1d9-4c29-aa19-008696cbf51e
-- title:
--   Single-clause gain is a concave endpoint-zero test
-- statement:
--   For any concave endpoint-zero test ψ and nonnegative coordinates v₀,v₁, the paper’s single-clause gain BₛΨ is concave in s on [0,1] and vanishes at s=0 and s=1. The proof includes zero coordinates.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Mathlib
open KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_clause_gain_concave (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    ConcaveOn ℝ (Icc 0 1) (softClauseGain ψ v0 v1) ∧
      softClauseGain ψ v0 v1 0 = 0 ∧ softClauseGain ψ v0 v1 1 = 0 := by sorry
