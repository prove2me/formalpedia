-- Prove2me | Theorems.Thm_OAI_Paper092_mem_standardSimplex_iff
-- name    : OAI.Paper092.mem_standardSimplex_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:14:27.324671+00:00
-- url     : https://prove2.me/theorems/1d56f3de-fa01-4a2d-a209-4b7e2c094330
-- title:
--   Inequality description of the standard simplex $\operatorname{conv}\{0,e_1,\dots,e_n\}$
-- statement:
--   Let $n\in\mathbb{N}$ and let $T_n=\operatorname{conv}\{0,e_1,\dots,e_n\}\subset\mathbb{R}^n$ be the standard simplex, the convex hull of the origin and the standard basis vectors of Euclidean space $\mathbb{R}^n$. For every $x=(x_1,\dots,x_n)\in\mathbb{R}^n$,
--
--   $$x\in T_n\iff x_i\ge0\ \text{for all } i\in\{1,\dots,n\}\ \text{ and }\ \sum_{i=1}^n x_i\le1 .$$
--
--   This converts the vertex description of the simplex into a description by $n+1$ linear inequalities. It is the basic input for working with $T_n$ in coordinates: membership tests, its facet structure, its volume $1/n!$, and the description of the product $T_{10}\times T_{10}$ by $22$ inequalities.
--
--   **Formalization Note** The simplex is `standardSimplex n`, defined as `convexHull ℝ (insert 0 (Set.range fun i => EuclideanSpace.single i 1))` in `EuclideanSpace ℝ (Fin n)`, with coordinates indexed by `Fin n`. The case $n=0$ is included; there both sides describe the single point of $\mathbb{R}^0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexCoordinates.lean#L13-L58

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry

open OAI OAI.Paper092
open Set
open scoped BigOperators

theorem OAI.Paper092.mem_standardSimplex_iff {n : ℕ} (x : Euclidean n) :
    x ∈ standardSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by sorry
