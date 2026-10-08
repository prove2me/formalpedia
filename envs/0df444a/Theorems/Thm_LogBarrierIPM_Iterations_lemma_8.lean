-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_lemma_8
-- name    : LogBarrierIPM.Iterations.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:07:24.348283+00:00
-- url     : https://prove2.me/theorems/3e66ab2f-badb-41a9-b9a8-23bba0497f55
-- title:
--   Lemma 8 — $d_\infty(S^{\mathrm{trop}},\log_t S)\le\log_t 2$ for a segment $S=[u,v]$
-- statement:
--   Let $t>1$, let $u,v\in\mathbb R^d$ with non-negative coordinates, let $S=[u,v]$ be the segment between them, and let $S^{\mathrm{trop}}=\mathsf{tsegm}(\log_t u,\log_t v)$ be the tropical segment between their logarithms (with $\log_t0=-\infty$). Then
--   $$d_\infty\big(S^{\mathrm{trop}},\log_t S\big)\le\log_t2,$$
--   where $\log_tS=\{\log_ts:\ s\in S\}$ and $d_\infty(X,Y)=\sup_{x\in X}\inf_{y\in Y}d_\infty(x,y)$ is the directed Hausdorff distance for the metric $d_\infty$ on $\mathbb T^d$.
--
--   Every point of the tropical segment is thus within $\log_t2$ of the logarithmic image of the ordinary segment, a bound that vanishes as $t\to\infty$. The paper uses it to pass from the ordinary segments of an interior point method to tropical segments.
--
--   **Formalization Note** The hypotheses $t>1$ and $u,v\ge0$ are implicit on the page: $\log_t$ of a coordinate is only defined for non-negative numbers (p. 7), and for $0<t<1$ the right-hand side $\log_t2$ is negative while the left-hand side is non-negative, so the inequality cannot hold. Distances are in `EReal`.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 11, Lemma 8

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_TropicalSegment
import Definitions.Def_LogBarrierIPM_Iterations_LogMetrics

namespace LogBarrierIPM.Iterations

/-- Lemma 8 (p. 11). Let `t > 1`, let `S = [u, v]` be a segment in `ℝ^d` with `u, v ≥ 0`, and let
`S^trop = tsegm(log_t u, log_t v)`. Then `d_∞(S^trop, log_t S) ≤ log_t 2`, where `d_∞(X, Y)` is the
directed Hausdorff distance `sup_{x ∈ X} inf_{y ∈ Y} d_∞(x, y)` and `log_t 0 = −∞`. -/
theorem lemma_8 {d : ℕ} (t : ℝ) (ht : 1 < t) (u v : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hv : ∀ i, 0 ≤ v i) :
    dInfSet (tsegm (logtVec t u) (logtVec t v)) (logtVec t '' segment ℝ u v) ≤
      ((Real.logb t 2 : ℝ) : EReal) := by sorry

end LogBarrierIPM.Iterations
