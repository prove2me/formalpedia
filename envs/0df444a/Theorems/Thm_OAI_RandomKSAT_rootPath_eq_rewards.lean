-- Prove2me | Theorems.Thm_OAI_RandomKSAT_rootPath_eq_rewards
-- name    : OAI.RandomKSAT.rootPath_eq_rewards
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:08:10.500026+00:00
-- url     : https://prove2.me/theorems/47041eef-5e4a-40cf-a994-3bd8854e1b94
-- title:
--   Path rewards of the refreshed pair chain equal prefix rewards of the refreshed root data
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Fix natural numbers $k,u$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   Fix a root assignment $a\in\{0,1\}^k$. *Refresh noise* is a tuple $z=(z_\star,(z_j)_{j\in[k]})$ with $z_\star\in\mathcal C_{u,k}$ and $z_j\in\mathcal C_{u,k-1}$. The *refreshed datum* $\rho_a(p,z)=(t,c')$ keeps the root pattern of $p=(t,c)$ and replaces its outer clause by $c'=z_\star$ if $|t|=0$, by $c'=z_j$ if $|t|=1$ and the unique root $j$ of $t$ is satisfied by $a$ (that is, $t(j)=a_j$), and keeps $c'=c$ otherwise.
--
--   Let $(p_i)_{i\in\mathbb N}$ be an environment of root data, let $f$ be any real function on subsets of $\{0,1\}^k\times\{0,1\}^u$, let $M\in\mathbb N$, let $z^{(0)},\dots,z^{(M-1)}$ be refresh noises, and let $S\subseteq\{0,1\}^k\times\{0,1\}^u$. Put $q_i=\rho_a(p_i,z^{(i)})$. The *path reward* is the reward collected along the trajectory of the refreshed pair chain,
--
--   $$
--   X_0=S,\qquad X_{i+1}=X_i\cap\mathrm{Sat}(q_i),\qquad \mathrm{Path}=\sum_{i=0}^{M-1} f(X_i),
--   $$
--
--   defined recursively by $\mathrm{Path}_0=0$ and $\mathrm{Path}_{M+1}=f(S)+(\text{path reward of length } M \text{ from } S\cap\mathrm{Sat}(q_0)$ for the shifted environment $(p_{i+1})_i$ and noise $(z^{(i+1)})_i)$.
--
--   **Theorem.** The path reward equals the prefix reward of the refreshed data:
--
--   $$
--   \mathrm{Path}=\sum_{m=0}^{M-1} f\Big(\big\{x\in S:\ x\in\mathrm{Sat}(q_i)\ \text{for all } i<m\big\}\Big).
--   $$
--
--   This identity converts the dynamic description (a Markov chain driven by the noise) into a static description in terms of the prefixes of the single word $(q_0,\dots,q_{M-1})$ of refreshed root data. It is used to move between second-moment estimates for the chain and statements about random sequences of root data.
--
--   **Formalization Note** The left side is `pathReward (pairEvolution a env) f M z S` and the right side is `dataRewards f S (fun i => refreshData a (env i) (z i))`, where `dataRewards f S ps` sums `f (pairPrefix S ps m)` over $m<M$. No hypothesis such as $k\le u$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/PairEvolution.lean#L166-L181

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.rootPath_eq_rewards {u k : ℕ} (a : Assignment k) (env : ℕ → RootData u k)
    (f : PairState u k → ℝ) (M : ℕ) (z : Fin M → RefreshNoise u k) (S : PairState u k) :
    pathReward (pairEvolution a env) f M z S =
      dataRewards f S (fun i => refreshData a (env i) (z i)) := by sorry
