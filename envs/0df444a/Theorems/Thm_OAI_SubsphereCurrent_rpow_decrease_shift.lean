-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_rpow_decrease_shift
-- name    : OAI.SubsphereCurrent.rpow_decrease_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:22:24.545578+00:00
-- url     : https://prove2.me/theorems/43da3e42-2d73-4eb5-9f9d-b75f156bebd1
-- title:
--   Raising the exponent of $x\ge 1/2$ costs at most a factor $2^{D}$
-- statement:
--   Let $x,a,A,D$ be real numbers with $x\ge\frac12$, $a\le A$ and $A-a\le D$. Then
--   $$
--   x^{a-1}\le 2^{D}\,x^{A-1},
--   $$
--   where all powers are real powers (of the positive numbers $x$ and $2$).
--
--   For $x\ge 1/2$, increasing the exponent of $x$ from $a-1$ to $A-1$ can decrease the power by at most the factor $2^{A-a}$, which is bounded by $2^D$. The inequality is used to dominate a beta density $q\mapsto q^{a-1}(1-q)^{b-1}/B(a,b)$ by $2^D$ times a beta density with a larger parameter on the half of $(0,1)$ where the relevant variable ($q$ or $1-q$) is at least $\frac12$, a step in comparing beta laws with nearby parameters.
--
--   **Formalization Note** The powers are `Real.rpow`; the base $x$ is positive because $x\ge 1/2$, so no convention for nonpositive bases is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Domination.lean#L112-L131

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination

open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.rpow_decrease_shift {x a A D : ℝ} (hx : (1 / 2 : ℝ) ≤ x)
    (ha : a ≤ A) (hD : A - a ≤ D) :
    x ^ (a - 1) ≤ (2 : ℝ) ^ D * x ^ (A - 1) := by sorry
