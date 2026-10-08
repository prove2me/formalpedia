-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_lemma_22
-- name    : LogBarrierIPM.Curvature.lemma_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:20:14.966017+00:00
-- url     : https://prove2.me/theorems/431d987f-ae61-409e-b98b-a87e91e1f437
-- title:
--   Lemma 22 — the angle $\angle\mathbf x(t)\mathbf y(t)$ of two Puiseux vectors has a limit, equal to $\pi/2$ when the arg maxes of the valuations are disjoint
-- statement:
--   Let $\mathbf x,\mathbf y\in\mathbb K^d$ be non-null vectors of absolutely convergent generalized real Puiseux series, and let $x:=\mathrm{val}(\mathbf x)$, $y:=\mathrm{val}(\mathbf y)\in\mathbb T^d$. Write $\angle\mathbf x(t)\mathbf y(t)\in[0,\pi]$ for the Euclidean angle between the real vectors $\mathbf x(t)$ and $\mathbf y(t)$. Then:
--
--   1. the limit of $\angle\mathbf x(t)\mathbf y(t)$ as $t\to+\infty$ exists;
--   2. if the sets $\arg\max_{i\in[d]}x_i$ and $\arg\max_{i\in[d]}y_i$ are disjoint, then
--   $$\lim_{t\to+\infty}\angle\mathbf x(t)\mathbf y(t)=\frac\pi2 .$$
--
--   This is the basic asymptotic fact that converts tropical (valuation) data into angles of the classical curves.
--
--   **Formalization Note** The angle is Mathlib's `InnerProductGeometry.angle` on `EuclideanSpace ℝ (Fin d)`, defined for every $t$ (it equals $\pi/2$ if a vector is $0$); since $\mathbf x(t)$ and $\mathbf y(t)$ are non-zero for all large $t$, the limits are those of the paper's angle. Limits are `Filter.Tendsto … atTop`.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 21, Lemma 22

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle

open Filter Topology

namespace LogBarrierIPM.Curvature

/-- Lemma 22 (p. 21). Let `x, y ∈ 𝕂^d` be non-null. Then `∠x(t)y(t)` has a limit as `t → +∞`, and
if `arg max_i val(x)_i` and `arg max_i val(y)_i` are disjoint, the limit is `π/2`. -/
theorem lemma_22 {d : ℕ} (x y : Fin d → Puiseux) (hx : IsNonNull x) (hy : IsNonNull y) :
    (∃ L : ℝ, Tendsto (fun t : ℝ => InnerProductGeometry.angle (evalVec x t) (evalVec y t))
        atTop (𝓝 L)) ∧
    (Disjoint (targmax (valVec x)) (targmax (valVec y)) →
      Tendsto (fun t : ℝ => InnerProductGeometry.angle (evalVec x t) (evalVec y t))
        atTop (𝓝 (Real.pi / 2))) := by sorry

end LogBarrierIPM.Curvature
