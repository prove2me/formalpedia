-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_proposition_7_6_9
-- name    : MDPFinance.InfiniteHorizonApplications.proposition_7_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:54.533137+00:00
-- url     : https://prove2.me/theorems/75ba4ff5-24e9-495d-9109-9a11c14e2907
-- title:
--   Proposition 7.6.9 — the two-arm joint K-stopping value shares the single-arm structure
-- statement:
--   Adding a "quit for $K$" option to the two-arm bandit produces a joint value function $\tilde
--   J(x;K)$ with the same monotonicity, continuity and convexity in $K$ as the single-arm $K$-stopping
--   value, and — the key structural fact that makes the whole Gittins-index reduction work — its own
--   threshold for quitting is exactly $I(x) := \max\{I(m_1,n_1),I(m_2,n_2)\}$, the *larger* of the two
--   arms' separately-computed single-arm indices: below that threshold, the optimal action is to pull
--   whichever arm attains that maximum.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 233, Proposition 7.6.9

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Proposition 7.6.9 (Bäuerle–Rieder, p. 233, PDF 244). Let `x \in \mathbb N_0^2 \times \mathbb
N_0^2` be fixed. Then it holds: a) `K \mapsto \tilde J(x;K)` is increasing, continuous and convex.
b) `K \mapsto \tilde J(x;K) - K` is decreasing. c) Let `I(x) := \max\{I(m_1,n_1),I(m_2,n_2)\}` for
`x = (m_1,n_1,m_2,n_2)` and `a^* \in \{1,2\}` the arm attaining the maximum. Then `\tilde J(x;K) =
K` if `K \ge I(x)`, `= p_{a^*}(x) + \beta(Q_{a^*}\tilde J)(x;K)` if `K < I(x) = I(m_{a^*},
n_{a^*})`. -/
theorem proposition_7_6_9 {β : ℝ} (KS : KStoppingValue β pMN) (JKS : JointKStoppingValue β)
    (x : BanditState2) :
    (Monotone (JKS.Jt · x) ∧ Continuous (JKS.Jt · x) ∧ ConvexOn ℝ Set.univ (JKS.Jt · x)) ∧
      Antitone (fun K => JKS.Jt K x - K) ∧
      (∀ astar : Fin 2, (astar = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1) →
        (astar = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2) →
        max (GittinsIndex KS x.1) (GittinsIndex KS x.2) =
          (if astar = 0 then GittinsIndex KS x.1 else GittinsIndex KS x.2) →
        (∀ K, max (GittinsIndex KS x.1) (GittinsIndex KS x.2) ≤ K → JKS.Jt K x = K) ∧
          ∀ K, K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2) →
            JKS.Jt K x = paBandit astar x + β * QaBandit astar (JKS.Jt K) x) := by sorry

end MDPFinance.InfiniteHorizonApplications
