-- Prove2me | Theorems.Thm_LG2021_Concentration_estimatorGood_full_gradient
-- name    : LG2021.Concentration.estimatorGood_full_gradient
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T17:02:03.725657+00:00
-- url     : https://prove2.me/theorems/f041d929-d072-45f7-a39e-d941695a5952
-- title:
--   Winner-local gradient confidence on the complete terminal history
-- statement:
--   Fix the same compact convex legal set, explicit configuration, complete history, normalized adaptive noise condition, candidate norm bounds, and paired-prefix confidence event as in the scalar confidence theorem. Assume additionally that the one-Lipschitz loss is globally convex and the confidence logarithm is nonnegative. Then, for every healthy actual trace state $p<N$, every retained comparison point, and the candidate selected by the actual stopping rule, its directional-gradient deviation is bounded by the published radius
--   $$2r\left(c\sqrt{\frac{H}{C m}}+\frac1{8rn}\right),$$
--   where $r,c,C$ are the configuration's radius, moment constant, and concentration constant, $H$ is its confidence logarithm, and $m$ is the actual sample count. The formal statement specifies the retained-point and winner conditions exactly. This transfers confidence from the paired observation prefix to the complete terminal history.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.estimatorGood_full_gradient {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hLip : LipschitzWith 1 F) (hconv : ConvexOn ℝ Set.univ F) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hN : N ≤ n) (hpair : 2*N ≤ n)
    (w : Seed d u n × (Fin n → ℝ)) (v : Fin (d+1) → Space d)
    (hH : 0 ≤ confidenceLog (oracleConfig d D n) u)
    (hseed : ∀ a k, ‖seedCandidates w.1 a k‖ ≤ (oracleConfig d D n).radius / (2*(d : ℝ)))
    (hg : historyPrefix hpair w ∈ estimatorGood (oracleConfig d D n) K hK.isClosed.measurableSet R anchor ν hνm N v) :
    ∀ p < N, (interior (codedBody K (traceState (oracleConfig d D n) K R w.1 (terminalPairs w.2) p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState (oracleConfig d D n) K R w.1 (terminalPairs w.2) p).1) →
      ∀ k, traceWinner (oracleConfig d D n) K R w.1 (terminalPairs w.2) p = some k → ∀ i,
      traceGradientDeviation (oracleConfig d D n) K R w.1 (terminalPairs w.2) F p k (v i) ≤
        2*(oracleConfig d D n).radius*((oracleConfig d D n).momentConstant*Real.sqrt
          (confidenceLog (oracleConfig d D n) u / ((oracleConfig d D n).concentrationConstant *
            (traceSampleCount (oracleConfig d D n) K R w.1 (terminalPairs w.2) p : ℝ))) +
              1/(8*(oracleConfig d D n).radius*(n : ℝ))) := by sorry
