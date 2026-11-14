-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_clause_gain_continuous
-- name    : KSATSingleFlip.Connect.soft_clause_gain_continuous
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:32:45.88717+00:00
-- url     : https://prove2.me/theorems/83399e18-b3ee-417f-bc3d-40faedbb08a8
-- title:
--   Continuity of the single-clause gain
-- statement:
--   For every continuous endpoint-zero test ψ and nonnegative coordinates v₀,v₁, the single-clause gain BₛΨ is continuous in s on [0,1], including cases with zero coordinates.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Mathlib
open KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_clause_gain_continuous (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc 0 1))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    ContinuousOn (softClauseGain ψ v0 v1) (Icc 0 1) := by sorry
