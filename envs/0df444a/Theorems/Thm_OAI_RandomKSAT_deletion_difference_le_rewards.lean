-- Prove2me | Theorems.Thm_OAI_RandomKSAT_deletion_difference_le_rewards
-- name    : OAI.RandomKSAT.deletion_difference_le_rewards
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:17:26.624651+00:00
-- url     : https://prove2.me/theorems/ca9028ee-3bf9-41fd-80ad-92a7cff7821e
-- title:
--   Deleting a root clause delays satisfiability by at most the forced-prefix reward
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Fix natural numbers $n,k,u,M$ and a bijection $e:[k]\sqcup[u]\to[n]$, which identifies root $j\in[k]$ with the variable $e(\mathrm{inl}\,j)$ and outer variable $v\in[u]$ with $e(\mathrm{inr}\,v)$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data. For $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ the *joined assignment* $e(x,b)\in\{0,1\}^n$ takes the value $x_j$ at $e(\mathrm{inl}\,j)$ and $b_v$ at $e(\mathrm{inr}\,v)$. The *merged clause* $\mu(p)$ of a root datum $p=(t,c)$ is the $k$-clause on $[n]$ with literal sign $t(j)$ at $e(\mathrm{inl}\,j)$ for each $j$ with $t(j)\neq\bot$, and with the literals of $c$ transported to the variables $e(\mathrm{inr}\,v)$.
--
--   For a sequence $\mathbf c=(c_0,\dots,c_{L-1})$ of clauses on $[n]$ and an index $i\in[L]$ define
--
--   $$
--   \mathrm T(\mathbf c)=\#\{m\in[L]:\ c_0,\dots,c_{m-1}\text{ have a common satisfying assignment}\},
--   $$
--
--   the first-failure time truncated at $L$, and let $\mathrm T_{\setminus i}(\mathbf c)$ be the number of $m\in[L]$ such that the clauses $c_j$ with $j<m$ and $j\neq i$ have a common satisfying assignment. For $a\in\{0,1\}^k$ and $P\subseteq\{0,1\}^k\times\{0,1\}^u$ the *forced indicator* is $\phi_a(P)=1$ if $P\neq\emptyset$ and every $(x,b)\in P$ has $x=a$, and $\phi_a(P)=0$ otherwise. For root data $\mathbf p=(p_0,\dots,p_{M-1})$ and $m\le M$ put $P_m(\mathbf p)=\{(x,b):(x,b)\in\mathrm{Sat}(p_l)\text{ for all } l<m\}$; the *forced-prefix reward* is $\sum_{m=0}^{M-1}\phi_a(P_m(\mathbf p))$.
--
--   **Theorem.** Let $i\in\{0,\dots,M\}$, let $c$ be a $k$-clause on $[n]$ and $a\in\{0,1\}^k$ such that for all $(x,b)$, $c$ is falsified by $e(x,b)$ if and only if $x=a$. Let $\mathbf c$ be the sequence of length $M+1$ obtained by inserting $c$ at position $i$ into $(\mu(p_0),\dots,\mu(p_{M-1}))$. Then
--
--   $$
--   \mathrm T_{\setminus i}(\mathbf c)-\mathrm T(\mathbf c)\ \le\ \sum_{m=0}^{M-1}\phi_a\big(P_m(\mathbf p)\big).
--   $$
--
--   The hypothesis says that $c$ is the clause on the $k$ root variables whose signs are opposite to $a$. The theorem compresses the effect of deleting one clause from a sequence into a quantity, the forced-prefix reward, that depends only on how the remaining clauses look from the root variables of $c$. Its second moment is then estimated probabilistically.
--
--   **Formalization Note** $\mathrm T$ and $\mathrm T_{\setminus i}$ are `finiteTime` and `omittedTime i`, the inserted sequence is `i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)`, the joined assignment is `joinedAssignment e`, and the reward is `dataRewards (forcedReward a) Finset.univ ps`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/OmissionCompression.lean#L116-L157

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
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.deletion_difference_le_rewards {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (a : Assignment k)
    (hc : ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a)
    (ps : Fin M → RootData u k) :
    omittedTime i (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) -
      finiteTime (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) ≤
      dataRewards (forcedReward a) Finset.univ ps := by sorry
