-- Prove2me | Theorems.Thm_OAI_TriangularCovering_mesh_abs_le
-- name    : OAI.TriangularCovering.mesh_abs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:47:44.354605+00:00
-- url     : https://prove2.me/theorems/9d6cdcfc-0214-4e77-9475-7e23d694f61f
-- title:
--   The points of the uniform mesh of $[-1,1]$ lie in $[-1,1]$
-- statement:
--   For a natural number $N\ge1$, the uniform mesh of $[-1,1]$ with $N$ cells has step $h_N=2/N$ and points
--   $$
--   m_{N,j}=-1+j\,h_N=-1+\frac{2j}{N}\qquad(j\in\mathbb{N}).
--   $$
--   For every natural number $j$ with $j\le N$,
--   $$
--   |m_{N,j}|\le1 .
--   $$
--
--   So all mesh points with index $0\le j\le N$, endpoints included, lie in $[-1,1]$. This is the bound $|a|,|b|\le1$ needed whenever a coefficient estimate is applied to a mesh cell $[a,b]=[m_{N,j},m_{N,j+1}]$ with $j<N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L326-L338

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.mesh_abs_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) : |mesh N j| ≤ 1 := by sorry
