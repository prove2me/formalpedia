-- Prove2me | Theorems.Thm_LG2021_Concentration_measure_scalarStageFailure_le
-- name    : LG2021.Concentration.measure_scalarStageFailure_le
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:34:11.46222+00:00
-- url     : https://prove2.me/theorems/5ef06a2f-9d64-4f1e-9c25-bb3c2ddc4ca5
-- title:
--   Adaptive scalar stage-confidence failure probability
-- statement:
--   For the concrete policy, fix its known configuration, a measurable legal action set $K$ with a legal fallback anchor, $u$ candidates, $N$ paired sampling iterations, and a confidence parameter $H\ge0$. Assume the loss lies in $[0,1]$ on $K$, the adaptive observation kernel satisfies the normalized conditional mean and exponential-square noise condition, $0<\lambda\le1/2$, $d\lambda\le1/2$, and $N\le\mathrm{horizon}+1$. Then the actual history law of the first $2N$ observations satisfies
--   $$\mathbb P(\texttt{scalarStageFailure})\le (N+1)^2u\,2e^{-H}.$$
--   The published failure event tests all interval endpoints and candidates using the actual history-dependent scalar estimator, its predictable mean, and its configured confidence threshold. Thus the statement covers every potential stage interval selected by the policy, including intervals selected after observing previous data. All observation kernels may depend measurably on the full previous legal history.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.measure_scalarStageFailure_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (H : ℝ) (hH : 0 ≤ H) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      (scalarStageFailure cfg K hK R anchor ν hνm N H) ≤
        ((N+1 : ℕ) : ℝ)^2 * u * (2 * Real.exp (-H)) := by sorry
