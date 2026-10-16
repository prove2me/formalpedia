-- Prove2me | Theorems.Thm_OAI_RandomKSAT_favg_pi_restrict
-- name    : OAI.RandomKSAT.favg_pi_restrict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:03:18.007367+00:00
-- url     : https://prove2.me/theorems/4b7964e9-9c5b-495e-bd12-2659fa140900
-- title:
--   Uniform average of a function of a sub-tuple over all tuples
-- statement:
--   For a finite set $Y$ and $h:Y\to\mathbb R$ write $\operatorname{avg}_{y\in Y}h(y)=\frac1{|Y|}\sum_{y\in Y}h(y)$ for the uniform average.
--
--   **Theorem.** Let $\iota$ and $\alpha$ be finite sets with $\alpha$ nonempty, let $p$ be a predicate on $\iota$ with $I=\{i\in\iota:\ p(i)\}$, and let $f:\alpha^{I}\to\mathbb R$. Then
--   $$
--   \operatorname*{avg}_{x\in\alpha^{\iota}}f\big(x|_{I}\big)=\operatorname*{avg}_{y\in\alpha^{I}}f(y),
--   $$
--   where $x|_I=(x_i)_{i\in I}$ is the restriction of the tuple $x$ to the coordinates in $I$.
--
--   In probabilistic terms: if $x$ is uniformly distributed on $\alpha^\iota$, then its restriction to any set of coordinates is uniformly distributed on the corresponding product. For example, when $x$ is a uniformly random family of clauses, an event that only involves the clauses indexed by $I$ has the same probability as for a fresh family of $|I|$ uniform clauses.
--
--   **Formalization Note** The average is `favg` (sum divided by cardinality). The nonemptiness of $\alpha$ ensures that averaging over the coordinates outside $I$ leaves unchanged a function that ignores them. The decidability instances on $\iota$ and $p$ are Lean bookkeeping.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiberRefresh.lean#L42-L59

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

theorem OAI.RandomKSAT.favg_pi_restrict.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (p : ι → Prop) [DecidablePred p] (f : ({i // p i} → α) → ℝ) :
    favg (fun x : ι → α => f (fun i => x i)) = favg f := by sorry
