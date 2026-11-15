-- Prove2me | Theorems.Thm_LG2021_Concentration_estimatorGood_failure_le
-- name    : LG2021.Concentration.estimatorGood_failure_le
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:48:05.409749+00:00
-- url     : https://prove2.me/theorems/35fac69f-a14f-4e4d-94d2-66d5f5e76904
-- title:
--   Simultaneous estimator confidence for the concrete adaptive policy
-- statement:
--   Let $d,n,u$ be positive integers, let $D\ge0$, and let $N\le n$. Run the concrete policy with the published configuration $\texttt{oracleConfig}(d,D,n)$ and $u$ candidates on a measurable legal set $K$ with a legal fallback anchor. Assume the unknown loss has values in $[0,1]$ on $K$ and the actual observation kernel satisfies the normalized conditional noise condition after every legal history. For any $d+1$ comparison points, the published simultaneous scalar and directional-gradient confidence event satisfies
--   $$\mathbb P(\texttt{estimatorGood}^{\mathsf c})\le\frac{3(d+2)}n$$
--   under the actual history law of the first $2N$ observations. This combines the two stage-confidence failure bounds with the explicit logarithmic confidence choice. Its event and probability law are those of the actual policy and seed distribution.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.estimatorGood_failure_le {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n) (hu : 0 < u)
    {D : ℝ} (hD : 0 ≤ D) (K : Set (Space d)) (hK : MeasurableSet K)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hN : N ≤ n) (v : Fin (d+1) → Space d) :
    (historyMeasure (policy (u := u) (oracleConfig d D n) K hK R anchor)
      (seedMeasure d u (oracleConfig d D n)) ν hνm (2*N)).real
      (estimatorGood (oracleConfig d D n) K hK R anchor ν hνm N v)ᶜ ≤ 3 * (d+2) / (n : ℝ) := by sorry
