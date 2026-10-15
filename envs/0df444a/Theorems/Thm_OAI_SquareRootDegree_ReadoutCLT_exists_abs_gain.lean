-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_ReadoutCLT_exists_abs_gain
-- name    : OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:40.368583+00:00
-- url     : https://prove2.me/theorems/d949b88b-c49e-4131-99d2-758c0aaf1cbf
-- title:
--   Normalized sums of a standardized variable have mean absolute value above a fixed Gaussian constant
-- statement:
--   Let $\alpha$ be a finite nonempty set with the uniform probability measure, and let $T:\alpha\to\mathbb{R}$ be standardized: $\mathbb{E}_{a\in\alpha}T(a)=0$ and $\mathbb{E}_{a\in\alpha}T(a)^2=1$. Let $\gamma$ be the standard Gaussian measure on $\mathbb{R}$, let $\varphi(u)=\tfrac12\max\big(0,1-2|u-1|\big)$ be one half of the unit-height tent of half-width $\tfrac12$ centered at $1$, and define the absolute constant
--
--   $$
--   c_0=\frac12\int_{\mathbb{R}}\varphi\,d\gamma .
--   $$
--
--   **Theorem.** There is an integer $n\ge1$ such that
--
--   $$
--   c_0<\mathbb{E}_{x\in\alpha^n}\Big|\frac{1}{\sqrt n}\sum_{j=1}^{n}T(x_j)\Big|,
--   $$
--
--   where $x=(x_1,\dots,x_n)$ is uniform on $\alpha^n$, i.e. $x_1,\dots,x_n$ are independent uniform samples from $\alpha$.
--
--   This is a soft consequence of the central limit theorem, with a lower bound $c_0$ that depends neither on $\alpha$ nor on $T$. It is used for the final read-out of the construction: applied to the standardized score of an observation $F$ of positive variance, it shows that the sign of the score of the $n$-fold grouped observation is a $\pm1$-valued function whose sum of degree-one Fourier coefficients exceeds $c_0\sqrt{n\,\mathrm{Var}(F)}$.
--
--   **Formalization Note** The constant is `ReadoutCLT.constant = (∫ x, test x ∂gaussianReal 0 1)/2` with `test x = (1/2) * tent 1 (1/2) x` and `tent a h x = max 0 (1 - |x-a|/h)`. The sum is `normalizedSum T n x = (Real.sqrt n)⁻¹ * ∑ i, T (x i)` and `average` is the uniform average over `Fin n → α`. The `MeasurableSpace` and `MeasurableSingletonClass` instances on `α` are only used to state the central limit theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/ReadoutCLT.lean#L38-L52

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

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.ReadoutCLT
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ constant < average (fun x => |normalizedSum T n x|) := by sorry
