-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Quarter_extend_norm_sq
-- name    : OAI.SubsphereCurrent.Quarter.extend_norm_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:54:08.302902+00:00
-- url     : https://prove2.me/theorems/66525767-a51f-4c4e-b7f5-3ede6bbf90c0
-- title:
--   Displacement of an isometry that turns a subspace by a right angle
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $F\subseteq E$ a linear subspace, with orthogonal projections $P_F$ onto $F$ and $P_{F^{\perp}}$ onto $F^{\perp}$. Let $e:F\to F$ be a linear isometric isomorphism of $F$ that turns every vector by a right angle, $\langle y,e(y)\rangle=0$ for all $y\in F$. Its *extension* $\hat e:E\to E$ acts as $e$ on $F$ and as the identity on $F^{\perp}$: $\hat e(x)=e(P_Fx)+P_{F^{\perp}}x$.
--
--   **Theorem.** For every $x\in E$,
--   $$
--   \lVert x-\hat e(x)\rVert^2=2\,\lVert P_Fx\rVert^2 .
--   $$
--
--   The extension is an isometry of $E$ that fixes $F^{\perp}$ pointwise, so it preserves all inner products with vectors of $F^{\perp}$; nevertheless it moves every point $x$ by exactly $\sqrt2\,\lVert P_Fx\rVert$. Such quarter turns exist on every even-dimensional $F$ (complex structures), and they produce points of the sphere that cannot be told apart by inner products with vectors of $F^{\perp}$ although they are far from each other.
--
--   **Formalization Note** The extension is `Quarter.extend F e`, obtained by conjugating `e` times the identity of $F^{\perp}$ with the isometry `F.orthogonalDecomposition` of $E$ onto the $\ell^2$ product of $F$ and $F^{\perp}$; the left-hand side is `dist x (extend F e x)^2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L818-L831

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

theorem OAI.SubsphereCurrent.Quarter.extend_norm_sq (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) (he : ∀ y, ⟪y,e y⟫ = 0)
    (x : E) : dist x (extend F e x)^2 = 2*‖F.orthogonalProjectionOnto x‖^2 := by sorry
