-- Prove2me | Theorems.Thm_LG2021_Concentration_exists_terminal_good_event
-- name    : LG2021.Concentration.exists_terminal_good_event
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T17:05:07.527676+00:00
-- url     : https://prove2.me/theorems/aeef76ea-7f5c-490c-af8d-436d6574f722
-- title:
--   Simultaneous terminal confidence event for the actual bandit policy
-- statement:
--   Let $d\ge1$ and $n\ge2$. Let $K\subseteq\mathbb R^d$ be compact and convex, with a known pairwise diameter bound $D\ge0$ and a legal fallback anchor. Let $F$ be globally convex and one-Lipschitz, with values in $[0,1]$ on $K$. Fix any $x_\star\in K$ and any $d+1$ comparison points, and let the observation kernel satisfy the normalized conditional mean and exponential-square noise condition after every legal history.
--
--   For the concrete policy with configuration $\texttt{oracleConfig}(d,D,n)$, its actual seed law, and its actual $n$-observation history law, there exists a measurable event $G$ such that
--   $$\mathbb P(G^{\mathsf c})\le\frac{100(d+2)}n.$$
--   Every history in $G$ satisfies the published structure $\texttt{TerminalGoodFacts}$: all candidate norms are bounded; all healthy-state scalar estimates satisfy their confidence radii; winner-local directional-gradient deviations satisfy their radii for retained comparison points; candidate hits hold whenever the reference point stays in all healthy coded bodies; and the actual cumulative loss obeys the paired-trace regret comparison. These are simultaneous facts about the concrete adaptive policy over all $n$ observation rounds. This is the probability-event interface used by the deterministic simplex-volume and regret closure.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Concentration.exists_terminal_good_event {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (F : Space d → ℝ) (hLip : LipschitzWith 1 F) (hconv : ConvexOn ℝ Set.univ F)
    (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1) (xstar : Space d) (hxstar : xstar ∈ K)
    (v : Fin (d+1) → Space d) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) :
    ∃ G : Set (Seed d (candidateCount n) n × (Fin n → ℝ)), MeasurableSet G ∧
      (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
        (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm n).real Gᶜ ≤
          100 * ((d : ℝ)+2) / (n : ℝ) ∧
      ∀ w ∈ G, TerminalGoodFacts (oracleConfig d D n) K hK.isClosed.measurableSet R anchor F xstar v w := by sorry
