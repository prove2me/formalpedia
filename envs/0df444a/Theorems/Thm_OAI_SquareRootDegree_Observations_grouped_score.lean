-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_Observations_grouped_score
-- name    : OAI.SquareRootDegree.Observations.grouped_score
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:09.453347+00:00
-- url     : https://prove2.me/theorems/8d1f914a-6633-41c9-9c4d-458b8d9f04bb
-- title:
--   The score of a block-repeated observation is the sum of the block scores
-- statement:
--   Let $\gamma$ and $\kappa$ be finite index sets and $\beta$ a finite set of labels. Points of a Boolean cube $\{\mathsf{false},\mathsf{true}\}^I$ are read as sign vectors via $\operatorname{sgn}(\mathsf{false})=1$, $\operatorname{sgn}(\mathsf{true})=-1$, and the cube sum is $\Sigma_I(x)=\sum_{i\in I}\operatorname{sgn}(x_i)$. For an observation $F:\{\mathsf{false},\mathsf{true}\}^I\to\beta$, its score is the conditional expectation of the cube sum given the observed label, for a uniformly random point:
--   $$\operatorname{sc}_F(x)=\mathbb E\big[\Sigma_I\,\big|\,F=F(x)\big]=\frac{\mathbb E_y\big[\mathbf 1[F(y)=F(x)]\,\Sigma_I(y)\big]}{\mathbb E_y\,\mathbf 1[F(y)=F(x)]}.$$
--
--   Now repeat an observation $F:\{\mathsf{false},\mathsf{true}\}^\gamma\to\beta$ on $|\kappa|$ disjoint blocks: a point $x$ of the cube $\{\mathsf{false},\mathsf{true}\}^{\kappa\times\gamma}$ has blocks $x^{(j)}=(x_{(j,i)})_{i\in\gamma}$ for $j\in\kappa$, and the grouped observation is $F^{\kappa}(x)=\big(F(x^{(j)})\big)_{j\in\kappa}\in\beta^\kappa$, whose score is taken with respect to the cube sum $\Sigma_{\kappa\times\gamma}$ of the large cube. Then for every $x\in\{\mathsf{false},\mathsf{true}\}^{\kappa\times\gamma}$,
--
--   $$
--   \operatorname{sc}_{F^{\kappa}}(x)=\sum_{j\in\kappa}\operatorname{sc}_F\big(x^{(j)}\big).
--   $$
--
--   So the best prediction of the total sign sum from the labels of all blocks is the sum of the per-block predictions. This additivity lets the score of a block-repeated observation be treated as a sum of independent copies of a single score, for instance when computing variances or applying central-limit arguments to grouped observations.
--
--   **Formalization Note** The score is `score F = conditionalAverage F cubeSum`, where `conditionalAverage F g x` is the cell moment of $g$ divided by the cell mass of the cell of $F(x)$; this mass is always positive here. The grouped observation is `grouped (κ := κ) F`. The decidable-equality assumptions on $\gamma$ and $\kappa$ are technical.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Observations.lean#L62-L81

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

theorem OAI.SquareRootDegree.Observations.grouped_score (F : Cube γ → β) :
    score (grouped (κ := κ) F) = fun x => ∑ j, score F (fun i => x (j,i)) := by sorry
