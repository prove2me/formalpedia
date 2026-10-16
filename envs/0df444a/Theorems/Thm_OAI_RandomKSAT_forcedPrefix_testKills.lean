-- Prove2me | Theorems.Thm_OAI_RandomKSAT_forcedPrefix_testKills
-- name    : OAI.RandomKSAT.forcedPrefix_testKills
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:09:35.936655+00:00
-- url     : https://prove2.me/theorems/3a1e4983-e7f8-45b0-85fe-514e406837cb
-- title:
--   A forced root assignment makes the hidden test clauses of an available root unsatisfiable on the fibre
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Fix natural numbers $k,u,M$ and a root assignment $a\in\{0,1\}^k$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   Let $p_0,\dots,p_{M-1}$ be root data, $p_i=(t_i,c_i)$, let $o_0,\dots,o_{M-1}\in\mathcal C_{u,k}$, and let $w_{j,i}\in\mathcal C_{u,k-1}$ for $j\in[k]$, $i\in[M]$ (the *hidden clauses*). The refreshed datum $q_i=(t_i,c_i')$ keeps $t_i$ and has outer clause $c_i'=o_i$ if $|t_i|=0$, $c_i'=w_{j,i}$ if $|t_i|=1$ and the unique root $j$ of $t_i$ satisfies $t_i(j)=a_j$, and $c_i'=c_i$ otherwise. For $m\in\mathbb N$ define
--
--   - $P_m=\{(x,b)\in\{0,1\}^k\times\{0,1\}^u:\ (x,b)\in\mathrm{Sat}(q_i)$ for all $i\in[M]$ with $i<m\}$;
--   - $F_m=\{b\in\{0,1\}^u:$ for all $i\in[M]$ with $i<m$, $b\in\mathrm{Sat}(o_i)$ if $|t_i|=0$ and $(a,b)\in\mathrm{Sat}(p_i)$ if $|t_i|\neq0\}$;
--   - $T_j(m)=\{i\in[M]: i<m,\ |t_i|=1,\ t_i(j)=a_j\}$, the *test times* at root $j$.
--
--   Call the root $j$ *available* if there is no $i\in[M]$ with $|t_i|\ge2$ such that $j$ is the unique root at which $t_i$ agrees with $a$ (that is, $t_i(j)=a_j$ and $t_i(l)\neq a_l$ for all $l\neq j$).
--
--   **Theorem.** Suppose every $(x,b)\in P_m$ has $x=a$, and the root $j$ is available. Then no point of $F_m$ satisfies all hidden clauses at the test times of $j$:
--
--   $$
--   \neg\,\exists\, b\in F_m\ \ \forall i\in T_j(m):\ b\in\mathrm{Sat}(w_{j,i}).
--   $$
--
--   The set $F_m$ is the fibre of $P_m$ over $a$, and it does not depend on the hidden clauses. The theorem says that whenever the surviving pairs are forced to have root part $a$, every available root carries a family of hidden clauses that kills this fibre. Since hidden clauses at different roots are independent, this is the source of the exponential smallness of forcing probabilities.
--
--   **Formalization Note** The environment is `env : Fin M → RootData u k`, the forcing hypothesis is stated for `pairPrefix Finset.univ (fun i => refreshData a (env i) (o i, fun j => ys j i)) m`, $F_m$ is `fibrePrefix a env o m`, availability is `Available a env j`, and the test condition is `TestAt a (env i) j`. Here $k-1$ is natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/PairEvolution.lean#L285-L318

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

theorem OAI.RandomKSAT.forcedPrefix_testKills {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ)
    (hforced : ∀ x ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m, x.1 = a)
    (j : Fin k) (hj : Available a env j) :
    ¬ ∃ b ∈ fibrePrefix a env o m,
      ∀ i : Fin M, i.val < m → TestAt a (env i) j → Satisfies (ys j i) b := by sorry
