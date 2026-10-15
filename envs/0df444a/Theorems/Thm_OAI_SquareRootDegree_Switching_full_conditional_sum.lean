-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_Switching_full_conditional_sum
-- name    : OAI.SquareRootDegree.Switching.full_conditional_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:58.392532+00:00
-- url     : https://prove2.me/theorems/f4e5ddfc-9e99-4e97-b91f-7accde6f7cfe
-- title:
--   Tower property for the switched observation: $g$ may be replaced by $\mathbb E[g\mid F]$ in the total sum
-- statement:
--   Let $\alpha$ be a finite nonempty set of inputs, $\beta$ a finite set of labels, $\iota$ a finite index set and $F:\alpha\to\beta$ a labelling. Consider the finite product set of points $((u,z),y)$ with $u\in\alpha$, old coordinates $z=(z_i)_{i\in\iota}\in\alpha^\iota$ and a new coordinate $y\in\alpha$, carrying the uniform distribution. Let $A$ be any predicate on old label tuples $\big(b,(b_i)_{i\in\iota}\big)\in\beta\times\beta^\iota$, and define the switched observation, with values in the disjoint union $(\beta\times\beta^\iota)\sqcup\beta$,
--   $$O((u,z),y)=\begin{cases}F(y) & \text{if } A\big(F(u),(F(z_i))_{i\in\iota}\big)\text{ holds},\\ \big(F(u),(F(z_i))_{i\in\iota}\big) & \text{otherwise}.\end{cases}$$
--   Thus, outside the event $A$ the old labels are revealed, and on the event only the label of the new coordinate is revealed. For $g:\alpha\to\mathbb R$ let $S_g((u,z),y)=g(u)+\sum_{i\in\iota}g(z_i)+g(y)$ be the total sum, and let $\hat g(a)=\mathbb E[g\mid F=F(a)]$ be the conditional average of $g$ given its label (uniform $a\in\alpha$). For a function $h$ on the product set, $\mathbb E[h\mid O]$ denotes the function whose value at a point $\omega$ is the uniform average of $h$ over the cell $\{O=O(\omega)\}$. Then
--
--   $$
--   \mathbb E\big[S_g\,\big|\,O\big]=\mathbb E\big[S_{\hat g}\,\big|\,O\big]\qquad\text{pointwise on the product set.}
--   $$
--
--   Because the switched observation depends on the inputs only through their labels, each coordinate function $g$ in the total sum may be replaced by its label-conditional average $\hat g$. This reduces the score of the switched observation to the label-conditional values of $g$, which is what the analysis of switching steps needs.
--
--   **Formalization Note** The product set is `FullSpace α ι = (α × (ι → α)) × α`, the observation is `observation F A` with values in `EventSpace β ι ⊕ β`, the total sum is `totalSum g`, and conditional averages are `conditionalAverage` (cell moment divided by cell mass; the cell of a point always has positive mass).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Switching.lean#L148-L163

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Switching
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

theorem OAI.SquareRootDegree.Switching.full_conditional_sum (F : α → β) (A : EventSpace β ι → Prop) (g : α → ℝ) :
    conditionalAverage (observation F A) (totalSum g) =
      conditionalAverage (observation F A) (totalSum (conditionalAverage F g)) := by sorry
