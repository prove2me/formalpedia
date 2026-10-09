-- Prove2me | Theorems.Thm_MKVDPP_Weak_eq_4_10
-- name    : MKVDPP.Weak.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:29:01.758981+00:00
-- url     : https://prove2.me/theorems/74be93f2-dcaf-490c-90da-38be30446694
-- title:
--   (4.10), p. 20 — V^M_W ↗ V_W, the graph of 𝒫̄^M_W is analytic, and (t,ν,M) ↦ V^M_W(t,ν) is upper semi-analytic
-- statement:
--   Under the standing assumptions:
--
--   1. for every $(t,\nu)\in[0,T]\times\mathcal P(\mathcal C^n)$, $M\mapsto V^M_W(t,\nu)$ is nondecreasing and $V^M_W(t,\nu)\to V_W(t,\nu)$ as $M\to\infty$;
--   2. the graph set $\{(t,\nu,M,\bar{\mathbb P}):\bar{\mathbb P}\in\bar{\mathcal P}^M_W(t,\nu)\}$ is an analytic subset of $[0,T]\times\mathcal P(\mathcal C^n)\times[0,\infty)\times\mathcal P(\bar\Omega)$;
--   3. the map
--   $$(t,\nu,M)\longmapsto V^M_W(t,\nu)\in[-\infty,\infty]$$
--   is upper semi-analytic.
--
--   These are the truncated analogues of Lemma 4.7, used to select near-optimal rules with controlled moments.
--
--   **Formalization Note** $M$ ranges over $[0,\infty)$ with its usual topology; convergence is in the order topology of $[-\infty,\infty]$.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 20, (4.10)

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **(4.10)** (p. 20). `V^M_W(t,ν) ↗ V_W(t,ν)` as `M ↗ ∞`; the graph
`{(t, ν, M, ℙ̄) : ℙ̄ ∈ 𝒫̄^M_W(t,ν)}` is analytic; `(t, ν, M) ↦ V^M_W(t,ν)` is upper semi-analytic. -/
theorem eq_4_10
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible) :
    (∀ t : ℝ≥0, t ≤ T → ∀ ν : ProbabilityMeasure (Cpath T n),
      Monotone (fun M : ℝ≥0 => VWM hπ c u₀ p t ν M) ∧
      Tendsto (fun M : ℝ≥0 => VWM hπ c u₀ p t ν M) atTop (𝓝 (VW c u₀ p π t ν))) ∧
    AnalyticSet (graphPbarWM hπ c u₀ p) ∧
    IsUpperSemianalytic
      (fun x : Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (Cpath T n) × ℝ≥0 =>
        VWM hπ c u₀ p x.1 x.2.1 x.2.2) := by sorry

end MKVDPP.Weak
