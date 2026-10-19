-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Quarter_extend_square_norm_sq
-- name    : OAI.SubsphereCurrent.Quarter.extend_square_norm_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:54:40.729131+00:00
-- url     : https://prove2.me/theorems/0519a2f3-e093-45b5-9736-63c5e430b224
-- title:
--   Displacement of the square of an isometry that squares to minus the identity on a subspace
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $F\subseteq E$ a linear subspace, with orthogonal projections $P_F$ onto $F$ and $P_{F^{\perp}}$ onto $F^{\perp}$. Let $e:F\to F$ be a linear isometric isomorphism with $e(e(y))=-y$ for all $y\in F$, and let $\hat e:E\to E$, $\hat e(x)=e(P_Fx)+P_{F^{\perp}}x$, be its extension acting as $e$ on $F$ and as the identity on $F^{\perp}$.
--
--   **Theorem.** For every $x\in E$,
--   $$
--   \lVert x-\hat e(\hat e(x))\rVert^2=4\,\lVert P_Fx\rVert^2 .
--   $$
--
--   Applying the extension twice reflects the $F$-component of $x$ through the origin and keeps its $F^{\perp}$-component, so it moves $x$ by $2\lVert P_Fx\rVert$. No orthogonality assumption $\langle y,e(y)\rangle=0$ is needed here. Combined with the companion identity $\lVert x-\hat e(x)\rVert^2=2\lVert P_Fx\rVert^2$ for quarter turns and the fact that $\hat e$ is an isometry, it shows that the three points $x$, $\hat e(x)$, $\hat e(\hat e(x))$, which have the same inner products with every vector of $F^{\perp}$, are pairwise at distance at least $\sqrt2\,\lVert P_Fx\rVert$.
--
--   **Formalization Note** The extension is `Quarter.extend F e`, defined through the isometry `F.orthogonalDecomposition` of $E$ onto the $\ell^2$ product of $F$ and $F^{\perp}$; the left-hand side is `dist x (extend F e (extend F e x))^2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L833-L847

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Quarter
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem OAI.SubsphereCurrent.Quarter.extend_square_norm_sq (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F)
    (he : ∀ y, e (e y) = -y) (x : E) :
    dist x (extend F e (extend F e x))^2 = 4*‖F.orthogonalProjectionOnto x‖^2 := by sorry
