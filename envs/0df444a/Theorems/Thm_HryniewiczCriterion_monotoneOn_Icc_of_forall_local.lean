-- Prove2me | Theorems.Thm_HryniewiczCriterion_monotoneOn_Icc_of_forall_local
-- name    : HryniewiczCriterion.monotoneOn_Icc_of_forall_local
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:47:25.407975+00:00
-- url     : https://prove2.me/theorems/77e80fee-11c2-489d-b3b0-bf71101269fe
-- title:
--   A function that is monotone near every point of $[0,T]$ is monotone on $[0,T]$
-- statement:
--   Let $E:\mathbb{R}\to\mathbb{R}$ and $T\in\mathbb{R}$. Suppose every $t_0\in[0,T]$ has a $\delta>0$ such that $E(s)\le E(t)$ whenever $s\le t$ both lie in $[0,T]\cap(t_0-\delta,t_0+\delta)$. Then $E$ is monotone on $[0,T]$. No continuity of $E$ is assumed (it is applied to integer-valued functions).
--   Proof idea: the balls $(t_0-\delta,t_0+\delta)$ cover the compact $[0,T]$; with a Lebesgue number $r$, any two points of $[0,T]$ at distance $<r$ lie in one ball, and $[s,t]$ is crossed in steps of length $r/2$.
-- source:
--   Elementary (Lebesgue number lemma); used for the local-to-global monotonicity of the eigen-angle defect in the proof of HryniewiczCriterion.positive_unitary_path_eigenAngleSum_le.

import Mathlib.Data.Real.Basic

theorem HryniewiczCriterion.monotoneOn_Icc_of_forall_local {E : ℝ → ℝ} {T : ℝ}
    (h : ∀ t0 ∈ Set.Icc 0 T, ∃ δ > 0, ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      |s - t0| < δ → |t - t0| < δ → s ≤ t → E s ≤ E t) :
    MonotoneOn E (Set.Icc 0 T) := by sorry
