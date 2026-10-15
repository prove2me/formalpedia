-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_Observations_singletonSum_eq_average
-- name    : OAI.SquareRootDegree.Observations.singletonSum_eq_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:07.106983+00:00
-- url     : https://prove2.me/theorems/40307499-f582-4d7c-81c8-b18e2a9b4198
-- title:
--   The sum of degree-one Fourier coefficients equals the correlation with the coordinate sum
-- statement:
--   Let $\Gamma$ be a finite set and read Boolean inputs as signs (false is $+1$, true is $-1$), so that $\mathcal C_\Gamma=\{-1,1\}^\Gamma$ carries the uniform probability measure. For $f:\mathcal C_\Gamma\to\mathbb{R}$ and $A\subseteq\Gamma$ the real Fourier coefficient is $\hat f(A)=\mathbb{E}_x\big[f(x)\prod_{i\in A}x_i\big]$. Then the sum of the degree-one coefficients of $f$ equals the correlation of $f$ with the coordinate sum:
--
--   $$
--   \sum_{i\in\Gamma}\hat f(\{i\})=\mathbb{E}_x\Big[f(x)\sum_{i\in\Gamma}x_i\Big].
--   $$
--
--   This identity turns the quantity $\sum_i\hat f(\{i\})$, which the main theorem compares with $\sqrt{\deg f}$, into a correlation with the linear form $x\mapsto\sum_ix_i$. It is used to evaluate this sum for sign read-outs of observations (where it becomes the mean absolute value of a conditional expectation), to see that it is unchanged under relabelling of the coordinates, and to see that it vanishes when $f$ is constant.
--
--   **Formalization Note** Inputs are `Cube γ = γ → Bool` with `sign false = 1` and `sign true = -1`. The left side is `singletonSum f = ∑ i, fourierCoeff f {i}` and the right side is the uniform `average` of `f x * cubeSum x` with `cubeSum x = ∑ i, sign (x i)`. The ambient finite type `β` of the section is omitted and plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Readout.lean#L16-L29

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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Readout

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype β] in
theorem OAI.SquareRootDegree.Observations.singletonSum_eq_average (f : Cube γ → ℝ) :
    singletonSum f = average (fun x => f x*cubeSum x) := by sorry
