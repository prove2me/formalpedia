-- Prove2me | Theorems.Thm_OAI_RandomKSAT_favg_pi_on
-- name    : OAI.RandomKSAT.favg_pi_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:21:27.332293+00:00
-- url     : https://prove2.me/theorems/8110bca1-104d-4f27-902a-3cd489c1b717
-- title:
--   Uniform averages of products over independent coordinates factorize
-- statement:
--   For a finite set $X$ and $h:X\to\mathbb{R}$ write $\mathbb E_{x\in X}[h(x)]=\frac{1}{|X|}\sum_{x\in X}h(x)$ for the uniform average. Let $\iota$ be a finite index set, $\alpha$ a finite nonempty set, and $\alpha^\iota$ the finite set of all maps $w:\iota\to\alpha$; under the uniform distribution on $\alpha^\iota$ the coordinates $w_i$ are independent and uniform on $\alpha$.
--
--   **Theorem.** For every subset $I\subseteq\iota$ and every function $f:\alpha\to\mathbb{R}$,
--   $$
--   \mathbb E_{w\in\alpha^\iota}\Big[\prod_{i\in I}f(w_i)\Big]=\Big(\mathbb E_{a\in\alpha}[f(a)]\Big)^{|I|}.
--   $$
--
--   This is the finite uniform form of the rule that the expectation of a product of functions of independent, identically distributed coordinates is the product of their expectations. With $|I|=2$ it computes, for instance, the probability that two independent uniform clauses both contain a given variable.
--
--   **Formalization Note** The statement is universe-polymorphic in $\iota$ and $\alpha$ and assumes decidable equality on $\iota$. Nonemptiness of $\alpha$ is used so that the average of the constant $1$ equals $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/HallSatisfiability.lean#L81-L98

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.favg_pi_on.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) (f : α → ℝ) :
    favg (fun w : ι → α => ∏ i ∈ I, f (w i)) = (favg f)^I.card := by sorry
