-- Prove2me | Theorems.Thm_OAI_RandomKSAT_rootRewards_square_conditioned
-- name    : OAI.RandomKSAT.rootRewards_square_conditioned
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:13:11.30699+00:00
-- url     : https://prove2.me/theorems/f9f15482-2b86-4d17-8bf0-69baaaf7a695
-- title:
--   Second moment of the forced-prefix reward for a fixed root environment
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Let $r\ge2$ and $u\ge r+1$ be integers, put $k=r+1$, and fix $a\in\{0,1\}^{k}$ and $M\in\mathbb N$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   Fix a root assignment $a\in\{0,1\}^k$. *Refresh noise* is a tuple $z=(z_\star,(z_j)_{j\in[k]})$ with $z_\star\in\mathcal C_{u,k}$ and $z_j\in\mathcal C_{u,k-1}$. The *refreshed datum* $\rho_a(p,z)=(t,c')$ keeps the root pattern of $p=(t,c)$ and replaces its outer clause by $c'=z_\star$ if $|t|=0$, by $c'=z_j$ if $|t|=1$ and the unique root $j$ of $t$ is satisfied by $a$ (that is, $t(j)=a_j$), and keeps $c'=c$ otherwise.
--
--   For $P\subseteq\{0,1\}^k\times\{0,1\}^u$ the *forced indicator* is $\phi_a(P)=1$ if $P\neq\emptyset$ and every $(x,b)\in P$ has $x=a$, and $\phi_a(P)=0$ otherwise.
--
--   Let $(p_i)_{i\in\mathbb N}$ be an environment of root data, $p_i=(t_i,c_i)$, of which only $p_0,\dots,p_{M-1}$ matter. Let $z^{(0)},\dots,z^{(M-1)}$ be independent uniform refresh noises and put $q_i=\rho_a(p_i,z^{(i)})$. Let $P_m=\{(x,b):(x,b)\in\mathrm{Sat}(q_i)\text{ for all } i<m\}$, and define the *forced-prefix reward*
--
--   $$
--   R=\sum_{m=0}^{M-1}\phi_a(P_m),
--   $$
--
--   the number of prefixes after which the surviving pairs exist and all have root part $a$. Let $Z=\#\{i<M: |t_i|\neq0\}$ count the *incident* steps and $V=\#\{i<M:|t_i|\ge2\}$ the *collision* steps. Put $K=(2^{r+1}r)^{r}$, $C=4(2K)^{1/r}$, $\beta=\frac{r+1}{r}$, and define the *deletion constant* $Q(d)=(C+1)\,d^{\beta}$ for $d\in\mathbb N$. Let $h(M)=1+\log(M+1)$ if $r=2$ and $h(M)=1$ if $r\ge 3$. Write $Q=Q(\max(1,Z))$.
--
--   **Theorem.**
--
--   $$
--   \mathbb E_z\big[R^2\big]\ \le\ 8\,Q^2\,h(M)+2\,M\,Q\,V+M^2\,V(V-1).
--   $$
--
--   The three terms correspond to environments without collisions, with exactly one collision, and with at least two collisions. When the environment comes from random clauses at linear density, $Z$ and $V$ are small and the right side is of order $h(M)$. This is the conditional estimate behind the second-moment bound for the forced-prefix reward of random root data.
--
--   **Formalization Note** The average is `favg` over `Fin M → RefreshNoise u (r+1)`, and $R$ is `dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i))`. $Z$ and $V$ are the cardinalities of `incidentSet` and `collisionSet` of the first $M$ environment entries, $\max(1,Z)$ is taken in $\mathbb N$, $Q(\cdot)$ is `deletionQ (r+1)`, $C$ is `lifetimeC (r+1)` and $h(M)$ is `durationLog (r+1) M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/WeightedRewards.lean#L343-L380

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
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.rootRewards_square_conditioned {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) (env : ℕ → RootData u (r+1)) :
    let Z := (incidentSet (fun i : Fin M => env i)).card
    let V : ℝ := (collisionSet (fun i : Fin M => env i)).card
    let Q := deletionQ (r+1) (max 1 Z)
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      8*Q^2*durationLog (r+1) M + 2*M*Q*V + (M : ℝ)^2*V*(V-1) := by sorry
