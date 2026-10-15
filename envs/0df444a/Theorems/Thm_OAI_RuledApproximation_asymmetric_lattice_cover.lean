-- Prove2me | Theorems.Thm_OAI_RuledApproximation_asymmetric_lattice_cover
-- name    : OAI.RuledApproximation.asymmetric_lattice_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:44:41.696692+00:00
-- url     : https://prove2.me/theorems/6a8e1f08-d252-45e3-80d9-fa867c1c6eec
-- title:
--   Covering the plane by the lattice $\{(i+\alpha j,\ \beta i+j)\}$ when $0\le\alpha\beta<1$
-- statement:
--   Let $\alpha,\beta\in\mathbb{R}$ satisfy $0\le\alpha\beta<1$. Then for every point $(u_1,u_2)\in\mathbb{R}^2$ there are integers $i,j$ with
--   $$
--   |u_1-(i+\alpha j)|\le\tfrac12\qquad\text{and}\qquad|u_2-(\beta i+j)|\le\tfrac12.
--   $$
--   In other words, every point of the plane lies within maximum-norm distance $\tfrac12$ of the lattice $\{i(1,\beta)+j(\alpha,1):\ i,j\in\mathbb{Z}\}$, so the translates of the square $[-\tfrac12,\tfrac12]^2$ by the points of this lattice cover $\mathbb{R}^2$.
--
--   Only the product $\alpha\beta$ is constrained; either off-diagonal coefficient may be arbitrarily large. The symmetric case $\alpha=\beta=a$ with $|a|<1$ is the lattice estimate behind the covering of ruled surfaces near hyperbolic points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Lattice.lean#L50-L108

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.asymmetric_lattice_cover (alpha beta : ℝ)
    (hprod : 0 ≤ alpha * beta) (hprod' : alpha * beta < 1) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + alpha * j)| ≤ 1 / 2 ∧
      |u₂ - (beta * i + (j : ℝ))| ≤ 1 / 2 := by sorry
