-- Prove2me | Theorems.Thm_OAI_RandomKSAT_favg_refreshPart
-- name    : OAI.RandomKSAT.favg_refreshPart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:03:44.270305+00:00
-- url     : https://prove2.me/theorems/989009da-bb81-4af0-9b8c-df98b26f9904
-- title:
--   Refreshing the outer part of a clause preserves the uniform clause distribution
-- statement:
--   For $u,w\in\mathbb N$ let $\mathcal C_{u,w}$ be the set of clauses of width $w$ on the variables $[u]=\{0,\dots,u-1\}$, i.e. pairs $(V,\beta)$ of a $w$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$. For a finite set $Y$ and $h:Y\to\mathbb R$ write $\operatorname{avg}_{y\in Y}h(y)=\frac1{|Y|}\sum_{y\in Y}h(y)$ for the uniform average.
--
--   Fix $k\le u$. A *root type* is a map $t:\{0,\dots,k-1\}\to\{\mathrm T,\mathrm F,\bot\}$, recording the signs that a clause carries on $k$ distinguished root variables ($\bot$ means that the root variable does not occur); its size $|t|$ is the number of $j$ with $t(j)\neq\bot$. A root assignment $a\in\{\mathrm T,\mathrm F\}^k$ *satisfies* $t$ if $t(j)=a(j)$ for some $j$. The *refresh noise* is a pair $z=\big(z^0,(z^1_j)_{j<k}\big)\in\mathcal N=\mathcal C_{u,k}\times(\mathcal C_{u,k-1})^k$. For an outer clause $c\in\mathcal C_{u,k-|t|}$ the refreshed outer clause is
--   $$
--   \rho_{t,a}(c,z)=\begin{cases}z^0&\text{if } |t|=0,\\ z^1_{j^\ast}&\text{if } |t|=1 \text{ and } a \text{ satisfies } t,\\ c&\text{otherwise},\end{cases}
--   $$
--   where in the second case $j^\ast$ is the unique root position with $t(j^\ast)=a(j^\ast)$.
--
--   **Theorem.** If $k\le u$, then for every root type $t$, every $a\in\{\mathrm T,\mathrm F\}^k$ and every $f:\mathcal C_{u,k-|t|}\to\mathbb R$,
--   $$
--   \operatorname*{avg}_{c\in\mathcal C_{u,k-|t|}}\ \operatorname*{avg}_{z\in\mathcal N}f\big(\rho_{t,a}(c,z)\big)=\operatorname*{avg}_{c\in\mathcal C_{u,k-|t|}}f(c).
--   $$
--   In words: if $c$ is uniform and $z$ is independent uniform noise, then $\rho_{t,a}(c,z)$ is again uniform on $\mathcal C_{u,k-|t|}$.
--
--   A clause of width $k$ on $k+u$ variables decomposes into its root type $t$ and an outer clause of width $k-|t|$ on the remaining $u$ variables. The theorem is the fibrewise step in showing that resampling the outer part of a clause that has no root literal, or a single root literal satisfied by $a$, leaves the uniform distribution on clauses invariant.
--
--   **Formalization Note** Root types are `Fin k → Option Bool`, with `none` in the role of $\bot$; $\rho_{t,a}(c,z)$ is `refreshPart t a c z`, and `RefreshNoise u k` is `Clause u k × (Fin k → Clause u (k-1))`. The widths $k$ and $k-1$ are identified with $k-|t|$ in the respective cases through the cast bijection `clauseCastEquiv`, and $j^\ast$ is chosen by choice (`trueRoot`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiberRefresh.lean#L84-L111

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

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.favg_refreshPart {u k : ℕ} (hku : k ≤ u) (t : RootType k) (a : Assignment k)
    (f : Clause u (k-rootSize t) → ℝ) :
    favg (fun c => favg (fun z : RefreshNoise u k => f (refreshPart t a c z))) = favg f := by sorry
