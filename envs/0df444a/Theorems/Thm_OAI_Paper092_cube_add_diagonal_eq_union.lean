-- Prove2me | Theorems.Thm_OAI_Paper092_cube_add_diagonal_eq_union
-- name    : OAI.Paper092.cube_add_diagonal_eq_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:26:13.067223+00:00
-- url     : https://prove2.me/theorems/f1117f66-bb42-4d96-ae8d-15b4510b83ef
-- title:
--   The unit cube plus its main diagonal is the cube together with one extrusion cell per coordinate
-- statement:
--   Let $\iota$ be a finite nonempty index set and work in $\mathbb{R}^\iota$. Let $Q=[0,1]^\iota=\{x: 0\le x_j\le1\text{ for all }j\}$ be the unit cube, $\mathbf 1$ the all-ones vector, and $[0,\mathbf 1]=\{t\mathbf 1: 0\le t\le1\}$ the diagonal segment. For $i\in\iota$ define the extrusion cell
--   $$
--   C_i=\{x\in\mathbb{R}^\iota:\ 1\le x_i\le2\ \text{ and }\ x_i-1\le x_j\le x_i\ \text{ for all } j\ne i\}.
--   $$
--
--   **Theorem.** With $+$ denoting Minkowski sum,
--   $$
--   Q+[0,\mathbf 1]=Q\ \cup\ \bigcup_{i\in\iota}C_i .
--   $$
--
--   Sliding the cube along its main diagonal sweeps out the cube itself together with one cell for each coordinate; in $C_i$ the coordinate $x_i$ is the largest one and lies in $[1,2]$. In the surrounding development this decomposition is used to compute the volume $|\iota|+1$ of the zonotope $Q+[0,\mathbf 1]$, each cell being the image of the cube under a volume-preserving affine shear.
--
--   **Formalization Note** $Q$ is `unitCube ι` (the order interval `Icc 0 1` in the function space `ι → ℝ`), $C_i$ is `extrusionCell i`, and $[0,\mathbf 1]$ is `segment ℝ 0 1`. The index type carries `Fintype`, `DecidableEq` and `Nonempty` instances; nonemptiness is what allows choosing a largest coordinate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/Extrusion.lean#L151-L202

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion

open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped ENNReal Pointwise
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.Paper092.cube_add_diagonal_eq_union [Nonempty ι] :
    unitCube ι + segment ℝ (0 : ι → ℝ) 1 =
      unitCube ι ∪ ⋃ i, extrusionCell i := by sorry
