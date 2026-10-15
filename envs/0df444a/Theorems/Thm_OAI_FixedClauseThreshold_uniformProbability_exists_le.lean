-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_uniformProbability_exists_le
-- name    : OAI.FixedClauseThreshold.uniformProbability_exists_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:58:32.795777+00:00
-- url     : https://prove2.me/theorems/f692db21-a44d-4680-9c5f-f3e0baca1633
-- title:
--   Union bound for uniform probabilities on finite sets
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets and let $p(a,b)$ be any property of pairs $(a,b)\in\alpha\times\beta$. For a property $q$ of elements of $\alpha$ write
--
--   $$
--   \Pr_a\big[q(a)\big]=\frac{\#\{a\in\alpha:\ q(a)\}}{\#\alpha}
--   $$
--
--   for its probability under the uniform distribution on $\alpha$. Then
--
--   $$
--   \Pr_a\big[\exists\,b\in\beta:\ p(a,b)\big]\ \le\ \sum_{b\in\beta}\Pr_a\big[p(a,b)\big].
--   $$
--
--   This is the union bound (Boole's inequality) for the events $\{a:\ p(a,b)\}$, $b\in\beta$, in the uniform finite setting used throughout the random $k$-SAT arguments. It underlies first-moment estimates such as summing over all candidate satisfying assignments, or over all candidate configurations that witness unsatisfiability.
--
--   **Formalization Note** $\Pr_a$ is `uniformProbability`, the cardinality ratio. When $\alpha$ is empty both sides are $0$ by the convention $0/0=0$, so no nonemptiness hypothesis is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterBounds.lean#L18-L34

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.uniformProbability_exists_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) :
    uniformProbability (fun a => ∃ b, p a b) ≤ ∑ b, uniformProbability (fun a => p a b) := by sorry
