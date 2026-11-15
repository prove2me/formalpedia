-- Prove2me | Theorems.Thm_LG2021_Concentration_measure_gradientStageFailure_le
-- name    : LG2021.Concentration.measure_gradientStageFailure_le
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:38:55.048143+00:00
-- url     : https://prove2.me/theorems/8b591215-33ba-46b7-9e24-7d5b2df3de0f
-- title:
--   Adaptive directional-gradient stage-confidence failure probability
-- statement:
--   For the concrete policy, fix its known configuration, a measurable legal action set $K$ with a legal fallback anchor, $u$ candidates, $N$ paired sampling iterations, a confidence parameter $H\ge0$, and $d+1$ fixed comparison points $v_0,\ldots,v_d$. Assume unit-range losses on $K$, the normalized adaptive conditional noise condition, $0<\lambda\le1/2$, $d\lambda\le1/2$, and $N\le\mathrm{horizon}+1$. Under the actual law of the first $2N$ observations,
--   $$\mathbb P(\texttt{gradientStageFailure})\le (N+1)^2u(d+1)\,2e^{-H}.$$
--   The published event tests the actual directional-gradient errors over all interval endpoints, candidates, and comparison directions in the quadratic Bernstein regime specified by the event. Its directions and active-stage tests are predictable functions of the observation history. The probability bound therefore applies directly to the adaptive policy, without an independent-stage assumption.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.measure_gradientStageFailure_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (H : ℝ) (hH : 0 ≤ H) (v : Fin (d+1) → Space d) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      (gradientStageFailure cfg K hK R anchor ν hνm N H v) ≤
        ((N+1 : ℕ) : ℝ)^2 * u * (d+1) * (2 * Real.exp (-H)) := by sorry
