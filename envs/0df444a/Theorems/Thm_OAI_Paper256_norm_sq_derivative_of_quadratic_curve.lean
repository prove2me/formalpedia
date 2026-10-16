-- Prove2me | Theorems.Thm_OAI_Paper256_norm_sq_derivative_of_quadratic_curve
-- name    : OAI.Paper256.norm_sq_derivative_of_quadratic_curve
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:41:44.012988+00:00
-- url     : https://prove2.me/theorems/87a33f42-1b09-45d4-9c31-cea95d42f51c
-- title:
--   An exact formula $\|f(s)\|^2=\frac{s^2}{1+s^2\beta}\alpha$ determines $\|f'(0)\|^2=\alpha$
-- statement:
--   Let $F$ be a real normed vector space, let $f:\mathbb{R}\to F$, $v\in F$, and $\alpha,\beta\in\mathbb{R}$ with $\beta\ge0$. Assume that $f$ is differentiable at $0$ with $f'(0)=v$, that $f(0)=0$, and that
--   $$
--   \|f(s)\|^2=\frac{s^2}{1+s^2\beta}\,\alpha\qquad\text{for all } s\in\mathbb{R}.
--   $$
--   Then
--   $$
--   \|v\|^2=\alpha .
--   $$
--
--   An exact formula for the norm of a curve through the origin thus determines the norm of its velocity at the origin. The lemma is used to turn an exact identity for the squared norm along a curve of kernel projections into an identity for the squared norm of their derivative, in a tangent-space computation.
--
--   **Formalization Note** Differentiability is `HasDerivAt f v 0`. The hypothesis $\beta\ge0$ makes the denominator $1+s^2\beta$ positive, so Lean's convention $a/0=0$ never comes into play.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/TangentLimit.lean#L14-L33

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped Topology
open Filter
universe u

theorem OAI.Paper256.norm_sq_derivative_of_quadratic_curve
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (v : F) (α β : ℝ) (hβ : 0 ≤ β)
    (hf : HasDerivAt f v 0) (hzero : f 0 = 0)
    (hval : ∀ s : ℝ, ‖f s‖ ^ 2 = s ^ 2 / (1 + s ^ 2 * β) * α) :
    ‖v‖ ^ 2 = α := by sorry
