-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_joint_index_action_dominates
-- name    : MDPFinance.InfiniteHorizonApplications.joint_index_action_dominates
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T02:50:31.798087+00:00
-- url     : https://prove2.me/theorems/3b668dac-9e6a-41b9-8a75-f087e0e206de
-- title:
--   A maximal Gittins index attains the largest joint continuation value
-- statement:
--   Consider two independent Beta-Bernoulli arms with posterior states $x=(i_1,i_2)$ and discount factor $0<\beta<1$. Let $J(i;K)$ and $\widetilde J(x;K)$ be the bounded single-arm and joint stopping values with retirement payment $K$, and let $I(i)=\inf\{K:J(i;K)=K\}$ be the single-arm Gittins index. Write $p_a(x)$ for arm $a$'s posterior success probability and $Q_a$ for the corresponding one-step transition operator.
--
--   Suppose arm $a^*$ has a maximal index, allowing either arm when the indices tie. For every payment $K<\max\{I(i_1),I(i_2)\}$ and either arm $a$,
--   $$
--   p_a(x)+\beta\bigl(Q_a\widetilde J(\cdot;K)\bigr)(x)
--   \le p_{a^*}(x)+\beta\bigl(Q_{a^*}\widetilde J(\cdot;K)\bigr)(x).
--   $$
--
--   This is the continuation-action comparison in Proposition 7.6.9(c). It isolates the index-based selection of an arm from regularity of the stopping value and the characterization of its retirement region, so those parts can be proved separately.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 233, Proposition 7.6.9(c), continuation-action comparison. https://link.springer.com/chapter/10.1007/978-3-642-18324-9_7

import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MDPFinance.InfiniteHorizonApplications

theorem MDPFinance.InfiniteHorizonApplications.joint_index_action_dominates
    {β : ℝ} (KS : KStoppingValue β pMN) (JKS : JointKStoppingValue β)
    (x : BanditState2) (astar : Fin 2)
    (h0 : astar = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1)
    (h1 : astar = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2)
    (K : ℝ) (hK : K < max (GittinsIndex KS x.1) (GittinsIndex KS x.2)) (a : Fin 2) :
    paBandit a x + β * QaBandit a (JKS.Jt K) x ≤
      paBandit astar x + β * QaBandit astar (JKS.Jt K) x := by sorry
