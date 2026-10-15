-- Prove2me | Theorems.Thm_OAI_RuledApproximation_nilpotent_frame
-- name    : OAI.RuledApproximation.nilpotent_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:55:21.321497+00:00
-- url     : https://prove2.me/theorems/74c6b646-b331-446c-811a-acba95fe1640
-- title:
--   A square-zero operator on the Euclidean plane is a shear in a suitable orthonormal frame
-- statement:
--   Let $A:\mathbb{R}^2\to\mathbb{R}^2$ be a linear map of the Euclidean plane with $A\circ A=0$. Then there exist a linear isometry $R$ of the Euclidean plane and a real number $d$ such that
--   $$R^{-1}A\,R\,z=(d\,z_2,\ 0)\qquad\text{for all } z=(z_1,z_2)\in\mathbb{R}^2 .$$
--   Equivalently, in the orthonormal basis $Re_1,Re_2$ the matrix of $A$ is $\begin{pmatrix}0&d\\0&0\end{pmatrix}$. No bound on $d$ is asserted; $d=0$ occurs exactly when $A=0$.
--
--   Square-zero (nilpotent) planar operators are thus orthogonally conjugate to elementary shears. In the covering argument this normal form is applied to the derivative of a field with square-zero derivative: in the resulting orthonormal coordinates the linearized flow $x\mapsto x+r\,Ax$ just slides horizontal rows, which is the input for the sliding-row lattice model, and orthonormality guarantees that coordinate squares correspond to genuine congruent squares in the plane.
--
--   **Formalization Note** $A$ is a continuous linear map `Plane →L[ℝ] Plane` with `A.comp A = 0`, where `Plane = EuclideanSpace ℝ (Fin 2)`; $R$ is a linear isometric equivalence `Plane ≃ₗᵢ[ℝ] Plane`, and the conclusion reads `R.symm (A (R z)) = vec2 (d * z 1) 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean#L12-L77

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.nilpotent_frame (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ d : ℝ, ∀ z : Plane,
      R.symm (A (R z)) = vec2 (d * z 1) 0 := by sorry
