-- Prove2me | Theorems.Thm_FragLOB_Collapse_theorem_1
-- name    : FragLOB.Collapse.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:47.010292+00:00
-- url     : https://prove2.me/theorems/4fff5323-a817-42e4-98b2-22be8e1285c4
-- title:
--   Theorem 1 (State Space Collapse), pp. 1331–1332 (with a.e. rationality and W* > 0) — equilibria are exactly liftings of workload equilibria
-- statement:
--   Consider the fragmented limit order book market with $N$ exchanges: dedicated limit-order rates $\lambda_i \ge 0$, optimizing limit-order rate $\Lambda > 0$, market-order rate $\mu > 0$, attraction coefficients $\beta_i > 0$, and arbitrary effective rebates $\tilde r_0,\dots,\tilde r_N$. Investor types $\gamma$ are distributed according to a probability measure $F$ on $[0,\infty)$ with finite mean.
--
--   1. **(Forward.)** Let $\pi^* \in \mathcal P$ be a routing decision and $W^* > 0$, and suppose that (i) $\pi^*$ is an optimal solution of the aggregated problem
--   $$\max_{\pi\in\mathcal P}\ \int_0^\infty \Big\{\pi_0(\gamma)\gamma\tilde r_0 + \sum_{i=1}^N \pi_i(\gamma)\Big(\gamma\tilde r_i - \frac{W^*}{\mu\beta_i}\Big)\Big\}\,dF(\gamma) \qquad (13)$$
--   and (ii) $\sum_{i=1}^N\big(\lambda_i + \Lambda\int_0^\infty \pi^*_i(\gamma)\,dF(\gamma)\big) = \mu$ (14). Then $(\pi^*, Q^*)$ is an equilibrium, where
--   $$Q^*_i = \Big(\lambda_i + \Lambda\int_0^\infty \pi^*_i(\gamma)\,dF(\gamma)\Big)\frac{W^*}{\mu\beta_i} \qquad (15).$$
--   2. **(Converse.)** If $(\pi^*, Q^*)$ is an equilibrium and $W^* = \beta^\top Q^*$, then $(\pi^*, W^*)$ satisfies (i) and (ii).
--
--   Here an equilibrium (Definition 1) is a pair $(\pi^*, Q^*)$ with $\pi^* \in \mathcal P$, $Q^* \in \mathbb R^N_+$, $\beta^\top Q^* > 0$, such that for $F$-almost every type $\gamma$ the vector $\pi^*(\gamma)$ maximizes $\pi_0\gamma\tilde r_0 + \sum_i \pi_i(\gamma\tilde r_i - \mathrm{ED}_i(Q^*))$ over the simplex, and $\lambda_i + \Lambda\int_0^\infty\pi^*_i\,dF = \mu_i(Q^*) = \mu\beta_iQ^*_i/\beta^\top Q^*$ for every exchange $i$.
--
--   The theorem reduces the $N$-dimensional equilibrium problem to a one-dimensional one in the workload: equilibria are exactly the liftings, through (15), of solutions of the workload problem (13)–(14).
--
--   **Formalization Note.** Three changes to the printed statement, each needed for it to be true and meaningful. (a) Individual rationality in Definition 1 is required for $F$-almost every type instead of every $\gamma \ge 0$: as printed the forward direction fails (for $N = 1$, $\lambda_1 = 0$, $\Lambda = 2$, $\mu = \beta_1 = 1$, $\tilde r = (-1,1)$, $F$ exponential with mean 1, the policy "post iff $\gamma > \ln 2$" with $W^* = 2\ln 2$ satisfies (13)–(14), and redefining it to "market order" at the single type $\gamma = 5$ keeps (13)–(14) but violates (10) at $\gamma = 5$). (b) $W^* > 0$ in the forward direction, and $\beta^\top Q^* > 0$ in the equilibrium: with $\Lambda = \mu = 1$ in the same example, $W^* = 0$ satisfies (13)–(14) but (15) gives $Q^* = 0$, where (4) is $0/0$. (c) $F$ has finite mean, so that the objective of (13) is a genuine integral for every routing decision. The paper's assumption that $F$ has a differentiable CDF with continuous density (p. 1329) is not used by Theorem 1 and is dropped, so the statement here is more general. The rebate assumptions ($\tilde r_0 < 0$, Assumption 1) are not imposed. Integrals $\int_0^\infty\cdots dF$ are taken over $\mathbb R$ against $F$, which charges no negative type. At an empty exchange the delay is $W/(\mu\beta_i)$, the value (12) assigns.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), pp. 1331–1332, Theorem 1 (State Space Collapse), with Definition 1 (p. 1331)

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem theorem_1 {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) :
    (∀ (pi : ℝ → Fin (N + 1) → ℝ) (W : ℝ), 0 < W → IsAggOptimal M F W pi →
        AggBalance M F pi → IsEquilibrium M F pi (lift M F pi W)) ∧
      (∀ (pi : ℝ → Fin (N + 1) → ℝ) (Q : Fin N → ℝ), IsEquilibrium M F pi Q →
        IsAggOptimal M F (workload M Q) pi ∧ AggBalance M F pi) := by sorry

end FragLOB.Collapse
