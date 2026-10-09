-- Prove2me | Theorems.Thm_MKVDPP_Weak_lemma_4_7
-- name    : MKVDPP.Weak.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:30:44.868591+00:00
-- url     : https://prove2.me/theorems/4e62e5a5-56b7-4704-8a07-71cf1dc1eabd
-- title:
--   Lemma 4.7, p. 18 — the graphs of 𝒫̂_W and 𝒫̄_W are analytic and V_W is upper semi-analytic
-- statement:
--   Under the standing assumptions, the graph sets
--   $$[\![\hat{\mathcal P}_W]\!]:=\{(t,\hat\nu,\bar{\mathbb P}):\bar{\mathbb P}\in\hat{\mathcal P}_W(t,\hat\nu)\},\qquad [\![\bar{\mathcal P}_W]\!]:=\{(t,\nu,\bar{\mathbb P}):\bar{\mathbb P}\in\bar{\mathcal P}_W(t,\nu)\}$$
--   are analytic subsets of $[0,T]\times\mathcal P(\hat\Omega)\times\mathcal P(\bar\Omega)$ and $[0,T]\times\mathcal P(\mathcal C^n)\times\mathcal P(\bar\Omega)$ respectively. Moreover the value function $V_W:[0,T]\times\mathcal P(\mathcal C^n)\to[-\infty,\infty]$ is upper semi-analytic.
--
--   This is the measurability half of Theorem 3.1.
--
--   **Formalization Note** The spaces of probability measures carry the topology of weak convergence; analytic sets are Mathlib's `AnalyticSet`.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 18, Lemma 4.7

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Lemma 4.7** (p. 18). The graph sets `⟦𝒫̂_W⟧` and `⟦𝒫̄_W⟧` are analytic subsets of
`[0,T] × 𝒫(Ω̂) × 𝒫(Ω̄)` and `[0,T] × 𝒫(𝒞ⁿ) × 𝒫(Ω̄)`, and `V_W` is upper semi-analytic. -/
theorem lemma_4_7
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible) :
    AnalyticSet (graphPhatW hπ c u₀ p) ∧ AnalyticSet (graphPbarW hπ c u₀ p) ∧
      IsUpperSemianalytic
        (fun x : Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (Cpath T n) => VW c u₀ p π x.1 x.2) := by sorry

end MKVDPP.Weak
