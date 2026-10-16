-- Prove2me | Theorems.Thm_OAI_RandomKSAT_rootRewards_square_density
-- name    : OAI.RandomKSAT.rootRewards_square_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:16:39.640356+00:00
-- url     : https://prove2.me/theorems/40e4b90f-cc64-4aab-bd2d-8d7b23aa3292
-- title:
--   Density form of the second-moment bound for forced-prefix rewards
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Let $r\ge2$ and $u\ge r+1$ be integers, put $k=r+1$, and fix $a\in\{0,1\}^k$ and $M\in\mathbb N$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   For $P\subseteq\{0,1\}^k\times\{0,1\}^u$ the *forced indicator* is $\phi_a(P)=1$ if $P\neq\emptyset$ and every $(x,b)\in P$ has $x=a$, and $\phi_a(P)=0$ otherwise. For $\mathbf p=(p_0,\dots,p_{M-1})\in\mathcal R_{u,k}^M$ let $P_m(\mathbf p)=\{(x,b):(x,b)\in\mathrm{Sat}(p_i)\text{ for all } i<m\}$ and define the *forced-prefix reward* $R(\mathbf p)=\sum_{m=0}^{M-1}\phi_a(P_m(\mathbf p))$, the number of prefixes after which the surviving pairs exist and all have root part $a$.
--
--   Let $K=(2^{r+1}r)^{r}$ and $C=4(2K)^{1/r}$. For real $A,D$ put, with $\mathrm e$ denoting Euler's number, $E=\exp\big((\mathrm e-1)A\big)$ and
--
--   $$
--   \mathcal D(A,D)=48\,\mathrm e\,(C+1)^2E+4\,\mathrm e^2\,(C+1)\,D\,E+D^2 .
--   $$
--
--   Let $h(M)=1+\log(M+1)$ if $r=2$ and $h(M)=1$ if $r\ge3$.
--
--   **Theorem.** Let $n$ be such that there is a bijection $\iota:[k]\sqcup[u]\to[n]$ (so $n=k+u$), and let $B\ge0$ be real with $M\le Bn$. If $\mathbf p$ is uniform on $\mathcal R_{u,k}^M$, then
--
--   $$
--   \mathbb E_{\mathbf p}\big[R(\mathbf p)^2\big]\ \le\ \mathcal D\big(B(r+1)^2,\ 2B^2(r+1)^4\big)\,h(M).
--   $$
--
--   When the number $M$ of clauses is at most linear in the number $n$ of variables, the second moment of the forced-prefix reward is therefore bounded by a constant depending only on $r$ and $B$, times $h(M)$, which equals $1$ for clause width at least $4$ and is logarithmic for clause width $3$. This is the form used to bound the squared effect of deleting one clause on the truncated satisfiability time, in the variance upper bound for the capped first-failure time.
--
--   **Formalization Note** The average is `favg` over `Fin M → RootData u (r+1)`, $R$ is `dataRewards (forcedReward a) Finset.univ ps`, $\mathcal D$ is `deletionMomentC (r+1)` and $h(M)$ is `durationLog (r+1) M`. The bijection $\iota$ is `e : Fin (r+1) ⊕ Fin u ≃ Fin n`; it only serves to identify root data with clauses on $[n]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SupportProbabilities.lean#L229-L246

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.rootRewards_square_density {n u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (e : Fin (r+1) ⊕ Fin u ≃ Fin n) (a : Assignment (r+1))
    {B : ℝ} (hB : 0 ≤ B) (hM : (M : ℝ) ≤ B*n) :
    favg (fun ps : Fin M → RootData u (r+1) => (dataRewards (forcedReward a) Finset.univ ps)^2) ≤
      deletionMomentC (r+1) (B*(r+1 : ℕ)^2) (2*B^2*(r+1 : ℕ)^4)*durationLog (r+1) M := by sorry
