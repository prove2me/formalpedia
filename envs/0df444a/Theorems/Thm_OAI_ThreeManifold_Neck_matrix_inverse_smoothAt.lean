-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
-- name    : OAI.ThreeManifold.Neck.matrix_inverse_smoothAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:33.992275+00:00
-- url     : https://prove2.me/theorems/f290edf2-7d9c-40ac-9258-7128b3cd4787
-- title:
--   The inverse of a smooth invertible $2\times 2$ matrix family is smooth
-- statement:
--   Let $R : \mathbb{R} \to \mathbb{R}^{2\times 2}$ be a family of real $2 \times 2$ matrices and $s \in \mathbb{R}$. If $R$ is $C^\infty$ at $s$ and $\det R(s) \ne 0$, then the family of inverses
--   $$
--   u \longmapsto R(u)^{-1}
--   $$
--   is $C^\infty$ at $s$.
--
--   This is a local smoothness statement for matrix inversion, used to show that the metric obtained by inverting a smooth cometric (or vice versa) is smooth wherever the matrix is nondegenerate.
--
--   **Formalization Note** "$C^\infty$ at $s$" is `ContDiffAt ℝ ∞` at $s$. Lean's matrix inverse is total: it is the zero matrix when the determinant vanishes. The hypothesis $\det R(s) \ne 0$ ensures that at $s$ this is the genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1728-L1744

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.matrix_inverse_smoothAt {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiffAt ℝ ∞ R s) (hdet : (R s).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => (R u)⁻¹) s := by sorry
