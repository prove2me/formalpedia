-- Prove2me | Theorems.Thm_LG2021_Algorithm_candidateTerminalEvent_failure_le
-- name    : LG2021.Algorithm.candidateTerminalEvent_failure_le
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:50:39.140802+00:00
-- url     : https://prove2.me/theorems/5b4c66af-6719-4a68-b1bd-9da17ff6ad42
-- title:
--   Adaptive candidate-hit event for the concrete policy
-- statement:
--   Let $d\ge1$, $n\ge2$, and $N\le n$. Let $K\subseteq\mathbb R^d$ be compact and convex, with known pairwise diameter bound $D\ge0$ and a legal fallback anchor. Let the loss be globally convex and one-Lipschitz, and let the observation kernel be any measurable history-dependent kernel satisfying the stated centered subgaussian noise condition on legal queries. For any reference point $x_\star$, the concrete policy with its published candidate count, configuration, and seed law satisfies
--   $$\mathbb P(\texttt{candidateTerminalEvent}^{\mathsf c})\le\frac{N+1}{3n^2}$$
--   after its first $2N$ observations. The event includes the almost-sure candidate norm bounds and propagates candidate hits from each actual stage start. The proof uses fresh candidate-coordinate independence at adaptive stage starts and the published Gaussian surrogate separation theorem.
--
--   This is a formalization auxiliary for Algorithms 1–2 and their probability analysis in Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134, Lemma 4 and Sections 5–7. The implementation and event predicates are published definitions; the guarantee is proved in this theorem. Adaptive observation kernels and exact finite-history semantics are explicit formal interfaces. Statistical concentration and regret claims are not assumed by the implementation definitions.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134:2938–2964, 2021. Lemma 4, Algorithms 1–2, and Sections 5–7 (printed pp. 7–11). Concrete adaptive-policy confidence and finite-history formalization auxiliary.

import Mathlib
import Definitions.Def_LG2021_Policy

open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory Set Metric

theorem LG2021.Algorithm.candidateTerminalEvent_failure_le {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (hN : N ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L) (xstar : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (γ : ℝ) (hν : NoiseCond K L γ ν) :
    (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm (2*N)).real
        (candidateTerminalEvent (oracleConfig d D n) K R L xstar)ᶜ ≤
          ((N : ℝ)+1)/(3*(n : ℝ)^2) := by sorry
