-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_compact_smoothing
-- name    : OAI.EuclideanRamsey.compact_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:04:32.789415+00:00
-- url     : https://prove2.me/theorems/1c753666-af27-4283-b940-5f765f5f63d3
-- title:
--   Smooth bumps for which $\tfrac12\sum C_{jl}\partial_j\partial_l b$ has arbitrarily small weighted negative part
-- statement:
--   For $k\in\mathbb{N}$, a real $k\times k$ matrix $C$ and a $C^2$ function $b:\mathbb{R}^k\to\mathbb{R}$, write
--   $$
--   L_Cb(x)=\frac12\sum_{j,l=1}^kC_{jl}\,\partial_j\partial_lb(x),
--   $$
--   and for a real $d\times k$ matrix $U$ write $|Ux|^2=\sum_{a=1}^d\big(\sum_{j=1}^kU_{aj}x_j\big)^2$ for the squared Euclidean norm of $Ux$.
--
--   **Theorem.** Let $k,d\in\mathbb{N}$ with $d\ge1$, let $C$ be a real symmetric $k\times k$ matrix, and let $U$ be a real $d\times k$ matrix with $UCU^{\top}=I_d$. Then for every $\eta>0$ there is a $C^\infty$ function $b:\mathbb{R}^k\to\mathbb{R}$ with compact support such that $b\ge0$, $\int_{\mathbb{R}^k}b(x)\,dx>0$ and
--
--   $$
--   \int_{\mathbb{R}^k}\max\big(-L_Cb(x),\,0\big)\,|Ux|^2\,dx\;<\;\eta\int_{\mathbb{R}^k}b(x)\,dx,
--   $$
--
--   where the integrals are with respect to Lebesgue measure.
--
--   The matrix $C$ may be indefinite, so $L_C$ need not be elliptic and $L_Cb$ can be negative on a large set. The theorem says that, after weighting by $|Ux|^2$, the negative part of $L_Cb$ can still be made an arbitrarily small fraction of the mass of a nonnegative bump. In the classification of Euclidean Ramsey configurations this continuous statement is subsequently discretized on fine lattices and rationalized, producing rational lattice measures with prescribed second moments and small weighted negative part.
--
--   **Formalization Note** The statement is the proposition `CompactSmoothing`. Here $L_Cb(x)$ is `stencilDifferential C b x = (1/2) * ∑ j, ∑ l, C j l * iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]`, the weight $|Ux|^2$ is `gradientWeight U x`, symmetry is `C.IsSymm`, and the condition on $U$ is `U * C * U.transpose = 1`. For $C^\infty$ compactly supported $b$ all integrands are continuous with compact support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean#L173-L234

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix

open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators
open MeasureTheory Matrix
open MeasureTheory Matrix
open scoped BigOperators

theorem OAI.EuclideanRamsey.compact_smoothing : CompactSmoothing := by sorry
