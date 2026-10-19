-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Weighted_nested_average
-- name    : OAI.SubsphereCurrent.Weighted.nested_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:51:35.032308+00:00
-- url     : https://prove2.me/theorems/fcc5b22c-5130-4b38-b9e0-a2fb8d56bf8b
-- title:
--   Averages over nested affine sections of the unit sphere
-- statement:
--   Work in $\mathbb{R}^d$ with unit sphere $S^{d-1}$. For a finite-dimensional real inner product space $X$ write $S(X)$ for its unit sphere and $\bar\sigma_X$ for the normalized surface measure on $S(X)$ (the uniform probability measure when $X\neq0$).
--
--   An *affine section* of dimension $n$ of $S^{d-1}$ is a triple $A=(V,c,\rho)$, where $V\subseteq\mathbb{R}^d$ is a linear subspace of dimension $n$, $c\in V^{\perp}$ and $\rho>0$ with $\lVert c\rVert^2+\rho^2=1$; it parametrizes the sphere $\{c+\rho v:\ v\in S(V)\}\subseteq S^{d-1}$ via $\phi_A(v)=c+\rho v$. A *slice* of dimension $k$ of the inner product space $V$ is a triple $B=(U,c',\rho')$, where $U\subseteq V$ is a subspace of dimension $k$, $c'\in V$ is orthogonal to $U$ and $\rho'>0$ with $\lVert c'\rVert^2+\rho'^2=1$; it gives the map $\psi_B(u)=c'+\rho'u$ from $S(U)$ to $S(V)$. The *nested section* $A\circ B$ is the affine section of dimension $k$ of $S^{d-1}$ with subspace $U'$ (the image of $U$ under the inclusion $V\subseteq\mathbb{R}^d$), center $c+\rho c'$ and radius $\rho\rho'$.
--
--   **Theorem.** For every measurable $g:S^{d-1}\to[0,\infty]$,
--   $$
--   \int_{S(U')}g\bigl(c+\rho c'+\rho\rho'\,w\bigr)\,d\bar\sigma_{U'}(w)=\int_{S(U)}g\bigl(c+\rho\,(c'+\rho' u)\bigr)\,d\bar\sigma_U(u).
--   $$
--
--   In other words, averaging $g$ over the nested section $A\circ B$ is the same as averaging $g\circ\phi_A$ over the slice $B$ of $S(V)$. This lets averages over affine sections be iterated: a slice of a section is again a section of the big sphere, with multiplied radius.
--
--   **Formalization Note** Affine sections are `Affine.Test d n`, slices are `Slice.Test A.space k` and the nested section is `nestedTest A B`; the parametrizations are `onTest A` and `B.point`, and $\bar\sigma_X$ is `Affine.sphereLaw X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L381-L400

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

theorem OAI.SubsphereCurrent.Weighted.nested_average {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s, g (onTest (nestedTest A B) s) ∂Affine.sphereLaw (nestedTest A B).space) =
      ∫⁻ s, g (onTest A (B.point s)) ∂Affine.sphereLaw B.space := by sorry
