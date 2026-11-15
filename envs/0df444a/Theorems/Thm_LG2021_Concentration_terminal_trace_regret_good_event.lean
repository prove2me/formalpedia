-- Prove2me | Theorems.Thm_LG2021_Concentration_terminal_trace_regret_good_event
-- name    : LG2021.Concentration.terminal_trace_regret_good_event
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:54:32.3382+00:00
-- url     : https://prove2.me/theorems/5836f8c0-6db8-4a06-be47-0b11097ad313
-- title:
--   Actual path-loss comparison on a terminal high-probability event
-- statement:
--   Consider the concrete policy with positive Gaussian radius on a compact convex legal set $K$, a legal fallback anchor, a globally convex one-Lipschitz loss with values in $[0,1]$ on $K$, and a measurable adaptive observation kernel satisfying the stated centered subgaussian condition. Let $N>0$ and $2N\le n\le2N+1$, with $N\le\mathrm{horizon}+1$, and fix any $x_\star\in K$. There exists a measurable event $G$, under the actual law of the first $n$ observations, with $\mathbb P(G^{\mathsf c})\le1/n$. On $G$, whenever the coded bodies have nonempty interior throughout the first $N$ paired iterations,
--   $$\sum_{t=1}^n L(X_t)-nL(x_\star)
--   \le 2\sum_{p=0}^{N-1}\min\{1,\Delta_p\}+\sqrt{n\log n}+1,$$
--   where $\Delta_p$ is the published actual-trace Gaussian comparator gap. The policy, seed law, full history measure, and gaps in this statement are concrete published definitions. The proof charges both observations in every paired iteration and the possible final unpaired observation.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.terminal_trace_regret_good_event {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {D : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hConv : ConvexOn ℝ univ L)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (N n : ℕ) (hN : N ≤ cfg.horizon + 1) (hNpos : 0 < N)
    (hpair : 2 * N ≤ n) (hodd : n ≤ 2 * N + 1)
    (xstar : Space d) (hxstar : xstar ∈ K) :
    ∃ G : Set (Seed d u cfg.horizon × (Fin n → ℝ)), MeasurableSet G ∧
      (historyMeasure (policy (u := u) cfg K hK.isClosed.measurableSet R anchor) (seedMeasure d u cfg)
        ν hνm n).real Gᶜ ≤ 1 / (n : ℝ) ∧
      ∀ w ∈ G,
        (∀ p < N, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty) →
        realPathLoss (policy (u := u) cfg K hK.isClosed.measurableSet R anchor) L w - (n : ℝ) * L xstar ≤
          2 * (∑ p ∈ Finset.range N, min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p)) +
            Real.sqrt ((n : ℝ) * Real.log n) + 1 := by sorry
