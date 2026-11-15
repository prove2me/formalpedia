-- Prove2me | Theorems.Thm_LG2021_Concentration_estimatorGood_full_scalar
-- name    : LG2021.Concentration.estimatorGood_full_scalar
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:56:57.496247+00:00
-- url     : https://prove2.me/theorems/798bc47b-ed73-4ff7-9a10-cd78b0dea579
-- title:
--   Scalar confidence on the complete terminal history
-- statement:
--   Fix $d,n\ge1$, $D\ge0$, a compact convex legal set with pairwise diameter bound $D$, and the published configuration. Assume a one-Lipschitz loss with unit range on the legal set and the normalized adaptive noise condition. Let $N\le n$ and $2N\le n$. For a complete $n$-observation history, suppose all candidate norms obey the configured bound and its first $2N$ observations lie in the published event $\texttt{estimatorGood}$. Then every scalar estimate at every healthy actual trace state $p<N$ and every candidate differs from its true surrogate gap by at most the published confidence radius at the actual sample count.
--
--   This is a deterministic implication about the complete terminal history. It connects the paired-prefix confidence event to the estimates used by the actual policy. The probability cost of that event is supplied separately by the simultaneous estimator-failure theorem.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.estimatorGood_full_scalar {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hLip : LipschitzWith 1 F) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hN : N ≤ n) (hpair : 2*N ≤ n)
    (w : Seed d u n × (Fin n → ℝ)) (v : Fin (d+1) → Space d)
    (hseed : ∀ a k, ‖seedCandidates w.1 a k‖ ≤ (oracleConfig d D n).radius / (2*(d : ℝ)))
    (hg : historyPrefix hpair w ∈ estimatorGood (oracleConfig d D n) K hK.isClosed.measurableSet R anchor ν hνm N v) :
    ∀ p < N, (interior (codedBody K (traceState (oracleConfig d D n) K R w.1 (terminalPairs w.2) p).1)).Nonempty → ∀ k,
      |traceScalar (oracleConfig d D n) K R w.1 (terminalPairs w.2) p k -
        traceGap (oracleConfig d D n) K R w.1 (terminalPairs w.2) F p k| ≤
      confidenceRadius (oracleConfig d D n) u (traceSampleCount (oracleConfig d D n) K R w.1 (terminalPairs w.2) p) := by sorry
