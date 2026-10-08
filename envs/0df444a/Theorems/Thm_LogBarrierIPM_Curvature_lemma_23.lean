-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_lemma_23
-- name    : LogBarrierIPM.Curvature.lemma_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:23.919524+00:00
-- url     : https://prove2.me/theorems/8664a410-44eb-4077-bed3-ae8622f5edf2
-- title:
--   Lemma 23 — the turning angle $\angle\mathbf U(t)\mathbf V(t)\mathbf W(t)$ tends to $\pi/2$ under the tropical conditions
-- statement:
--   Let $\mathbf U,\mathbf V,\mathbf W\in\mathbb K^d$ and $U:=\mathrm{val}(\mathbf U)$, $V:=\mathrm{val}(\mathbf V)$, $W:=\mathrm{val}(\mathbf W)\in\mathbb T^d$. Suppose
--   $$\max_{i\in[d]}U_i<\max_{i\in[d]}V_i<\max_{i\in[d]}W_i$$
--   and that $\arg\max_{i\in[d]}V_i$ and $\arg\max_{i\in[d]}W_i$ are disjoint. Then the turning angle at $\mathbf V(t)$ of the three real points $\mathbf U(t),\mathbf V(t),\mathbf W(t)$, i.e. the angle between $\mathbf V(t)-\mathbf U(t)$ and $\mathbf W(t)-\mathbf V(t)$, satisfies
--   $$\lim_{t\to+\infty}\angle\mathbf U(t)\mathbf V(t)\mathbf W(t)=\frac\pi2 .$$
--
--   It refines Lemma 22 to triples of successive points of a monotone tropical curve and motivates the weak tropical angle $\angle^*$.
--
--   **Formalization Note** The maxima are taken in $\mathbb T=$ `WithBot ℝ`. The turning angle is the module's `turningAngle`, which is $0$ on degenerate triples; under the hypotheses the three points are pairwise distinct for all large $t$, so the limit is the paper's.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 22, Lemma 23

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle

open Filter Topology

namespace LogBarrierIPM.Curvature

/-- Lemma 23 (p. 22). Let `U, V, W ∈ 𝕂^d` with `max_i val(U)_i < max_i val(V)_i < max_i val(W)_i`
and `arg max_i val(V)_i ∩ arg max_i val(W)_i = ∅`. Then the turning angle
`∠U(t)V(t)W(t)` tends to `π/2` as `t → +∞`. -/
theorem lemma_23 {d : ℕ} (U V W : Fin d → Puiseux)
    (hUV : tmax (valVec U) < tmax (valVec V)) (hVW : tmax (valVec V) < tmax (valVec W))
    (hdisj : Disjoint (targmax (valVec V)) (targmax (valVec W))) :
    Tendsto (fun t : ℝ => turningAngle (evalVec U t) (evalVec V t) (evalVec W t))
      atTop (𝓝 (Real.pi / 2)) := by sorry

end LogBarrierIPM.Curvature
