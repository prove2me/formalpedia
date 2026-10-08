-- Prove2me | Theorems.Thm_GradSampling_Conv_lemma_3_1
-- name    : GradSampling.Conv.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:30.502584+00:00
-- url     : https://prove2.me/theorems/e036f048-2b8b-4f3f-bf52-6e3fdac46d9a
-- title:
--   Lemma 3.1, p. 757 — ⟨v − u, −u/‖u‖⟩ ≤ [‖v‖√(2/η) + √(2‖ū‖ + δ)]√δ
-- statement:
--   Let $C\subseteq\mathbb R^n$ be a nonempty closed convex set with $0\notin C$, and let $v\in C$. If $\delta>0$, $\eta>0$, and $u,\bar u\in C$ satisfy $\eta\le\|\bar u\|=\operatorname{dist}(0\mid C)$ and $\|u\|\le\|\bar u\|+\delta$, then
--
--   $$\Big\langle v-u,\ \frac{-u}{\|u\|}\Big\rangle\le\Big[\|v\|\sqrt{\tfrac{2}{\eta}}+\sqrt{2\|\bar u\|+\delta}\Big]\sqrt\delta .$$
--
--   This quantifies how well the direction of a nearly least-norm element of $C$ separates $C$ from the origin; it is the estimate that produces the contradiction in the proof of Theorem 3.4.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 757, Lemma 3.1

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Lemma 3.1, p. 757. -/
theorem lemma_3_1 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) (hCcl : IsClosed C)
    (hCcv : Convex ℝ C) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ C) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ C)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (u ubar : EuclideanSpace ℝ (Fin n)) (hu : u ∈ C)
    (hubar : ubar ∈ C) (hηu : η ≤ ‖ubar‖) (hmin : ‖ubar‖ = Metric.infDist 0 C)
    (hle : ‖u‖ ≤ ‖ubar‖ + δ) :
    inner ℝ (v - u) (-(‖u‖⁻¹ • u)) ≤
      (‖v‖ * Real.sqrt (2 / η) + Real.sqrt (2 * ‖ubar‖ + δ)) * Real.sqrt δ := by sorry

end GradSampling.Conv
