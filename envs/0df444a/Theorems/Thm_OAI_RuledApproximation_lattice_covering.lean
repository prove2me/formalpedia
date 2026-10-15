-- Prove2me | Theorems.Thm_OAI_RuledApproximation_lattice_covering
-- name    : OAI.RuledApproximation.lattice_covering
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:45:12.359529+00:00
-- url     : https://prove2.me/theorems/0b0a802d-2d1d-43ed-9f86-015e6eee9f5a
-- title:
--   Symmetric lattice covering with a uniform bound on the integer displacement
-- statement:
--   Let $a\in\mathbb{R}$ with $|a|<1$, and let $(z_1,z_2)\in\mathbb{R}^2$. Then there are integers $i,j$ such that the displacement $x=z_1-i$, $y=z_2-j$ satisfies
--   $$
--   |x+ay|\le\tfrac12,\qquad|y+ax|\le\tfrac12,\qquad\max(|x|,|y|)\le\frac{1}{2(1-|a|)}.
--   $$
--   Equivalently, with $T_a=\begin{pmatrix}1&a\\a&1\end{pmatrix}$, every $z\in\mathbb{R}^2$ has an integer point $m\in\mathbb{Z}^2$ with $\|T_a(z-m)\|_\infty\le\tfrac12$ and $\|z-m\|_\infty\le\frac{1}{2(1-|a|)}$.
--
--   After rescaling by $1/n$, this is the lattice estimate for the hyperbolic linear model: for each label $p$ it provides a point $b$ of the lattice $\tfrac1n\mathbb{Z}^2$ such that $T_a(p-b)$ has sup norm at most $\tfrac1{2n}$, while $b$ itself stays within $\frac{1}{2(1-|a|)n}$ of $p$, uniformly as long as $|a|$ stays away from $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Lattice.lean#L132-L149

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.lattice_covering (a : ℝ) (ha : |a| < 1) (z₁ z₂ : ℝ) :
    ∃ i j : ℤ,
      |(z₁ - i) + a * (z₂ - j)| ≤ 1 / 2 ∧
      |(z₂ - j) + a * (z₁ - i)| ≤ 1 / 2 ∧
      max |z₁ - i| |z₂ - j| ≤ 1 / (2 * (1 - |a|)) := by sorry
