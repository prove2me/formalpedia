-- Prove2me | Theorems.Thm_OAI_RandomKSAT_integrated_occupationReward
-- name    : OAI.RandomKSAT.integrated_occupationReward
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:11:52.535256+00:00
-- url     : https://prove2.me/theorems/9b0cda67-7a5f-4106-93c3-fd808aeb0413
-- title:
--   Occupation bound for the block-killing reward along a scheduled clause chain
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Let $r\ge2$, $u\ge r+1$, $d\ge1$ and $M\ge0$ be integers. For $F\subseteq\{0,1\}^u$ let $\kappa(F)$ be the probability that $d$ independent uniformly random clauses in $\mathcal C_{u,r}$ have no common satisfying assignment in $F$. Put $K=(2^{r+1}r)^{r}$, $C=4(2K)^{1/r}$, $\beta=\frac{r+1}{r}$, and define the *deletion constant* $Q(d)=(C+1)\,d^{\beta}$ for $d\in\mathbb N$. Let $h(M)=1+\log(M+1)$ if $r=2$ and $h(M)=1$ if $r\ge 3$. Let $\gamma=(r+1)-\beta=\frac{(r+1)(r-1)}{r}$ and define the *occupation reward*
--
--   $$
--   g(F)=\begin{cases}\kappa(F)^{\gamma}, & F\neq\emptyset,\\ 0, & F=\emptyset.\end{cases}
--   $$
--
--   A *schedule* consists of a set of *ordinary* times $O\subseteq\mathbb N$ and masks $\Lambda_i\subseteq\{0,1\}^u$ for $i\in\mathbb N$. The associated scheduled chain started at $F$ is $F_0=F$, with $F_{i+1}=F_i\cap\mathrm{Sat}(c_i)$ for a fresh uniform $c_i\in\mathcal C_{u,r+1}$ (independent of everything else) if $i\in O$, and $F_{i+1}=F_i\cap\Lambda_i$ if $i\notin O$.
--
--   **Theorem.** Let $Z$ be a real number with $0\le Z\le d$ and suppose at most $Z$ of the times $0,1,\dots,M-1$ are not ordinary. Then for every $F\subseteq\{0,1\}^u$,
--
--   $$
--   \mathbb E\Big[\sum_{i=0}^{M-1} g(F_i)\Big]\ \le\ 4\,Q(d)\,h(M).
--   $$
--
--   The reward $g$ is large only on sets that $d$ random $r$-clauses kill with substantial probability, and such sets have short expected lifetime under random $(r+1)$-clauses. The theorem turns this into a bound on the total expected reward along any schedule with few non-ordinary steps. The bound is uniform in $u$ and $M$ except for the logarithmic factor in the critical case $r=2$, i.e. clause width $3$.
--
--   **Formalization Note** The left side is `markovSum (scheduledStep u (r+1) ordinary mask) (occupationReward u r d) M S`, the $M$-step occupation sum defined recursively by $\Sigma_0=0$ and $\Sigma_{m+1}(F)=g(F)+P_0\Sigma'_m(F)$, where $P_i$ is the averaging operator of step $i$ and $\Sigma'$ uses the shifted schedule; it equals the expectation above. $\kappa$ is `blockKill u r F d`, $\gamma$ is `occupationGamma (r+1)`, $Q(d)$ is `deletionQ (r+1) d`, $C$ is `lifetimeC (r+1)` and $h(M)$ is `durationLog (r+1) M`; powers with real exponents are `Real.rpow`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/WeightedRewards.lean#L231-L282

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

theorem OAI.RandomKSAT.integrated_occupationReward {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (ordinary : ℕ → Prop) [DecidablePred ordinary] (mask : ℕ → Finset (Assignment u))
    (M : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : (∑ i ∈ Finset.range M, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u (r+1) ordinary mask) (occupationReward u r d) M S ≤
      4*deletionQ (r+1) d * durationLog (r+1) M := by sorry
