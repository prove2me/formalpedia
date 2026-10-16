-- Prove2me | Theorems.Thm_OAI_RandomKSAT_forcedPrefix_probability
-- name    : OAI.RandomKSAT.forcedPrefix_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:10:06.922813+00:00
-- url     : https://prove2.me/theorems/a14e63c2-d523-4a03-8db5-dd5cd152ccf2
-- title:
--   Forcing probability is bounded by a power of the block-killing probability
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Fix natural numbers $k\le u$, $M$, $d$ and a root assignment $a\in\{0,1\}^k$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   Let $p_0,\dots,p_{M-1}$ be root data, $p_i=(t_i,c_i)$, and fix outer clauses $o_0,\dots,o_{M-1}\in\mathcal C_{u,k}$. Let $W=(w_{j,i})_{j\in[k],\,i\in[M]}$ be a family of independent uniformly random clauses in $\mathcal C_{u,k-1}$ (the *hidden clauses*). The refreshed datum $q_i=(t_i,c_i')$ keeps $t_i$ and has outer clause $c_i'=o_i$ if $|t_i|=0$, $c_i'=w_{j,i}$ if $|t_i|=1$ and the unique root $j$ of $t_i$ satisfies $t_i(j)=a_j$, and $c_i'=c_i$ otherwise. For a fixed $m\in\mathbb N$ let
--
--   - $P_m(W)=\{(x,b): (x,b)\in\mathrm{Sat}(q_i)$ for all $i\in[M]$ with $i<m\}$;
--   - $F_m=\{b\in\{0,1\}^u:$ for all $i\in[M]$ with $i<m$, $b\in\mathrm{Sat}(o_i)$ if $|t_i|=0$ and $(a,b)\in\mathrm{Sat}(p_i)$ if $|t_i|\neq0\}$, which does not depend on $W$;
--   - $T_j(m)=\{i\in[M]: i<m,\ |t_i|=1,\ t_i(j)=a_j\}$ for $j\in[k]$.
--
--   Root $j$ is *available* if no $i\in[M]$ with $|t_i|\ge2$ has $j$ as the unique root at which $t_i$ agrees with $a$. For $P\subseteq\{0,1\}^k\times\{0,1\}^u$ the *forced indicator* is $\phi_a(P)=1$ if $P\neq\emptyset$ and every $(x,b)\in P$ has $x=a$, and $\phi_a(P)=0$ otherwise. For $F\subseteq\{0,1\}^u$ and $g\in\mathbb N$, let $\kappa(F,g)$ be the probability that $g$ independent uniformly random clauses in $\mathcal C_{u,k-1}$ have no common satisfying assignment in $F$.
--
--   **Theorem.** Let $J\subseteq[k]$ consist of available roots and suppose $|T_j(m)|\le d$ for every $j\in[k]$. Then
--
--   $$
--   \mathbb E_W\big[\phi_a(P_m(W))\big]\ \le\ \mathbf 1[F_m\neq\emptyset]\cdot \kappa(F_m,d)^{|J|}.
--   $$
--
--   In words, for the surviving pairs to be forced to root part $a$, each available root must see its block of at most $d$ hidden clauses kill the fibre $F_m$. These blocks are independent, so the forcing probability is at most the $|J|$-th power of the block-killing probability. This is the probabilistic input that controls forced states in the second-moment estimates for clause deletion.
--
--   **Formalization Note** The average is `favg` over `Fin k → Fin M → Clause u (k-1)`. $\kappa$ is `blockKill u (k-1) F d`, defined through the law of an i.i.d. uniform clause stream (the first $d$ clauses), and $\mathbf 1[F\neq\emptyset]$ is `alive u F`. Here $k-1$ is natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/HiddenTests.lean#L109-L160

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.forcedPrefix_probability {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : Fin M → RootData u k) (o : Fin M → Clause u k) (m : ℕ)
    (J : Finset (Fin k)) (hJ : ∀ j ∈ J, Available a env j)
    (hd : ∀ j, (testIndices a env m j).card ≤ d) :
    favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m)) ≤
          alive u (fibrePrefix a env o m) * blockKill u (k-1) (fibrePrefix a env o m) d ^ J.card := by sorry
