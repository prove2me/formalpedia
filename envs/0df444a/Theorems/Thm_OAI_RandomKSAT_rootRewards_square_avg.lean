-- Prove2me | Theorems.Thm_OAI_RandomKSAT_rootRewards_square_avg
-- name    : OAI.RandomKSAT.rootRewards_square_avg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:16:09.621354+00:00
-- url     : https://prove2.me/theorems/c98dcef9-68a2-4884-9a01-2ade15151231
-- title:
--   Second moment of the forced-prefix reward for independent uniform root data
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Let $r\ge2$ and $u\ge r+1$ be integers, put $k=r+1$, and fix $a\in\{0,1\}^k$ and $M\in\mathbb N$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   For $P\subseteq\{0,1\}^k\times\{0,1\}^u$ the *forced indicator* is $\phi_a(P)=1$ if $P\neq\emptyset$ and every $(x,b)\in P$ has $x=a$, and $\phi_a(P)=0$ otherwise. For $\mathbf p=(p_0,\dots,p_{M-1})\in\mathcal R_{u,k}^M$ let $P_m(\mathbf p)=\{(x,b):(x,b)\in\mathrm{Sat}(p_i)\text{ for all } i<m\}$ and define the *forced-prefix reward* $R(\mathbf p)=\sum_{m=0}^{M-1}\phi_a(P_m(\mathbf p))$, the number of prefixes after which the surviving pairs exist and all have root part $a$.
--
--   For a uniformly random root datum $(t,c)\in\mathcal R_{u,k}$ let $\pi_{\mathrm{inc}}=\Pr[|t|\neq0]$ be the probability that it meets the roots, and $\pi_{\mathrm{col}}=\Pr[|t|\ge2]$ the probability that it meets at least two roots. Let $K=(2^{r+1}r)^{r}$ and $C=4(2K)^{1/r}$. For real $A,D$ put, with $\mathrm e$ denoting Euler's number, $E=\exp\big((\mathrm e-1)A\big)$ and
--
--   $$
--   \mathcal D(A,D)=48\,\mathrm e\,(C+1)^2E+4\,\mathrm e^2\,(C+1)\,D\,E+D^2 .
--   $$
--
--   Let $h(M)=1+\log(M+1)$ if $r=2$ and $h(M)=1$ if $r\ge3$.
--
--   **Theorem.** Let $A,D$ be real numbers with $M\pi_{\mathrm{inc}}\le A$ and $M^2\pi_{\mathrm{col}}\le D$. If $\mathbf p$ is uniform on $\mathcal R_{u,k}^M$ (that is, $p_0,\dots,p_{M-1}$ are independent uniform root data), then
--
--   $$
--   \mathbb E_{\mathbf p}\big[R(\mathbf p)^2\big]\ \le\ \mathcal D(A,D)\,h(M).
--   $$
--
--   Root data on $k$ roots and $u$ outer variables correspond bijectively to $k$-clauses on $k+u$ variables, so $\mathbf p$ encodes a sequence of independent uniform $k$-clauses seen from a fixed set of $k$ root variables. The theorem bounds the second moment of the forced-prefix reward, which controls the effect of deleting one clause on the truncated satisfiability time, in terms of an upper bound $A$ on the expected number $M\pi_{\mathrm{inc}}$ of root data meeting the roots and an upper bound $D$ on $M^2\pi_{\mathrm{col}}$, which is $M$ times the expected number of root data meeting at least two roots.
--
--   **Formalization Note** The average is `favg` over `Fin M → RootData u (r+1)`, $R$ is `dataRewards (forcedReward a) Finset.univ ps`, $\pi_{\mathrm{inc}}$ and $\pi_{\mathrm{col}}$ are `hitProbability rootIncident` and `hitProbability rootCollision`, $\mathcal D(A,D)$ is `deletionMomentC (r+1) A D`, $C$ is `lifetimeC (r+1)` and $h(M)$ is `durationLog (r+1) M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/CountMoments.lean#L260-L299

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.rootRewards_square_avg {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) {A D : ℝ}
    (hA : M*hitProbability (rootIncident (u := u) (k := r+1)) ≤ A)
    (hD : (M : ℝ)^2*hitProbability (rootCollision (u := u) (k := r+1)) ≤ D) :
    favg (fun ps : Fin M → RootData u (r+1) => (dataRewards (forcedReward a) Finset.univ ps)^2) ≤
      deletionMomentC (r+1) A D*durationLog (r+1) M := by sorry
