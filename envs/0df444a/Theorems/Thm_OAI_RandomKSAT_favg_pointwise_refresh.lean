-- Prove2me | Theorems.Thm_OAI_RandomKSAT_favg_pointwise_refresh
-- name    : OAI.RandomKSAT.favg_pointwise_refresh
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:04:32.708489+00:00
-- url     : https://prove2.me/theorems/b6f79874-288b-4661-b9fc-0b4dd2c133fa
-- title:
--   Applying a uniformity-preserving random map to each coordinate preserves the uniform distribution on tuples
-- statement:
--   For a finite set $Y$ and $h:Y\to\mathbb R$ write $\operatorname{avg}_{y\in Y}h(y)=\frac1{|Y|}\sum_{y\in Y}h(y)$ for the uniform average (with value $0$ if $Y=\emptyset$).
--
--   **Theorem.** Let $\alpha,\beta$ be finite sets and $R:\alpha\times\beta\to\alpha$ a map such that
--   $$
--   \operatorname*{avg}_{a\in\alpha}\ \operatorname*{avg}_{b\in\beta}g\big(R(a,b)\big)=\operatorname*{avg}_{a\in\alpha}g(a)\qquad\text{for every } g:\alpha\to\mathbb R .
--   $$
--   Then for every $m\in\mathbb N$ and every $f:\alpha^m\to\mathbb R$,
--   $$
--   \operatorname*{avg}_{x\in\alpha^m}\ \operatorname*{avg}_{z\in\beta^m}f\big(R(x_0,z_0),\dots,R(x_{m-1},z_{m-1})\big)=\operatorname*{avg}_{x\in\alpha^m}f(x).
--   $$
--
--   In probabilistic terms: if $R(a,b)$ is uniform on $\alpha$ whenever $a$ is uniform on $\alpha$ and $b$ is independent and uniform on $\beta$, then applying $R$ coordinatewise, with independent noise, to a uniform tuple again yields a uniform tuple. This is used to refresh all members of a uniformly random family at once (for instance the root data of all clauses of a random formula) without changing its distribution.
--
--   **Formalization Note** The average is `favg` (sum divided by cardinality), tuples are functions `Fin m → α`, and no nonemptiness assumption is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiberRefresh.lean#L151-L189

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

theorem OAI.RandomKSAT.favg_pointwise_refresh.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β]
    (R : α → β → α)
    (hR : ∀ f : α → ℝ, favg (fun a => favg (fun b => f (R a b))) = favg f)
    (m : ℕ) (f : (Fin m → α) → ℝ) :
    favg (fun x : Fin m → α => favg (fun z : Fin m → β => f (fun i => R (x i) (z i)))) =
      favg f := by sorry
