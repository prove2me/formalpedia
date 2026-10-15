-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_finiteClauseAverage_commute
-- name    : OAI.FixedClauseThreshold.finiteClauseAverage_commute
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:02:16.504772+00:00
-- url     : https://prove2.me/theorems/25aba47c-061d-4827-bbef-5342e1476264
-- title:
--   Averaging operators over two finite random clause families commute
-- statement:
--   Fix $n\in\mathbb N$ and let $\Omega=\{0,1\}^n$ be the set of truth assignments. Let $\mathcal C$ and $\mathcal D$ be finite sets of "clauses" with arbitrary satisfaction relations: for $c\in\mathcal C$ and $d\in\mathcal D$ let $\operatorname{Sat}(c),\operatorname{Sat}(d)\subseteq\Omega$ be the sets of assignments declared to satisfy them. For a real function $f$ on subsets of $\Omega$ define
--
--   $$
--   (A_{\mathcal C}f)(S)=\frac{1}{|\mathcal C|}\sum_{c\in\mathcal C}f\big(S\cap\operatorname{Sat}(c)\big)\qquad(S\subseteq\Omega),
--   $$
--
--   and $A_{\mathcal D}$ in the same way. Then $A_{\mathcal C}$ and $A_{\mathcal D}$ commute:
--
--   $$
--   A_{\mathcal C}\big(A_{\mathcal D}f\big)=A_{\mathcal D}\big(A_{\mathcal C}f\big)\qquad\text{for every }f .
--   $$
--
--   Probabilistically, restricting a solution set first by a random clause from one family and then by an independent random clause from the other has the same effect as the opposite order. Commutation is what allows iterates of different clause operators (proper clauses of different lengths, auxiliary clauses with repeated variables, clauses confined to a block of variables) to be reordered, compared with each other and expanded binomially.
--
--   **Formalization Note** $A_{\mathcal C}$ is `finiteClauseAverage satC`, where `satC : C → Assignment n → Prop` is the satisfaction relation, and the average is `uniformMean`; an average over an empty family is $0$, and the identity also holds in that degenerate case. The conclusion is stated as `Function.Commute`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Interpolation.lean#L53-L67

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
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.finiteClauseAverage_commute {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop) :
    Function.Commute (finiteClauseAverage satC) (finiteClauseAverage satD) := by sorry
