-- Prove2me | Theorems.Thm_GradSampling_Conv_epsSubdiff_closed_graph
-- name    : GradSampling.Conv.epsSubdiff_closed_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:30.664199+00:00
-- url     : https://prove2.me/theorems/b234a10f-8299-4600-88d9-7e4ede3a536e
-- title:
--   §2, p. 754 — the multifunction ∂̄_ε f has closed graph
-- statement:
--   Let $f$ be locally Lipschitz and $\epsilon>0$. Then the graph
--
--   $$\{(x,v)\in\mathbb R^n\times\mathbb R^n : v\in\bar\partial_\epsilon f(x)\}$$
--
--   is closed. Consequently, if $\operatorname{dist}(0\mid\bar\partial_\epsilon f(x^k))\to0$ along a subsequence converging to $\bar x$, then $0\in\bar\partial_\epsilon f(\bar x)$; this is the last step of the proof of Theorem 3.4.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 754, §2, "it is easily shown that the multifunction ∂̄_ε f has closed graph"

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- §2, p. 754: the multifunction `∂̄_ε f` has closed graph. -/
theorem epsSubdiff_closed_graph {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (ε : ℝ) (hε : 0 < ε) :
    IsClosed {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ epsSubdiff f ε p.1} := by sorry

end GradSampling.Conv
