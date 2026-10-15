-- Prove2me | Theorems.Thm_OAI_RuledApproximation_nilpotent_lattice_model
-- name    : OAI.RuledApproximation.nilpotent_lattice_model
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:56:31.891263+00:00
-- url     : https://prove2.me/theorems/6010f1a5-fffc-489a-89be-85240744650d
-- title:
--   Sliding-row lattice model for every real multiple of the elementary shear
-- statement:
--   Work in the coordinate plane $\mathbb{R}^2$ with the maximum norm $\|x\|_\infty=\max(|x_1|,|x_2|)$, and for an integer $n\ge1$ let $\tfrac1n\mathbb{Z}^2$ be the grid of points whose coordinates are integer multiples of $\tfrac1n$. A linear map $A$ of $\mathbb{R}^2$ satisfies the *lattice model with time bound $L$ and radius $R$* if for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r\in\mathbb{R}$ with $|r|\le L$ there is a grid point $b\in\tfrac1n\mathbb{Z}^2$ with $\|b-p\|_\infty\le R/n$ and $\|(p-b)+r\,A(p-b)\|_\infty\le\tfrac1{2n}$.
--
--   **Theorem.** Let $N(z_1,z_2)=(z_2,0)$ be the elementary shear and let $d\in\mathbb{R}$. Then $dN$ satisfies the lattice model with time bound $L=1$ and radius $R=(1+|d|)/2$. Explicitly, for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r$ with $|r|\le1$ there are integers $i,j$ such that $b=(i/n,\,j/n)$ satisfies
--   $$\|b-p\|_\infty\le\frac{1+|d|}{2n},\qquad \bigl|(p_1-b_1)+r\,d\,(p_2-b_2)\bigr|\le\frac1{2n},\qquad |p_2-b_2|\le\frac1{2n}.$$
--
--   In words: for every time $r\in[-1,1]$, the point $(I+r\,dN)p$ lies within max-distance $\tfrac1{2n}$ of the image $(I+r\,dN)b$ of a grid point $b$ that is itself within $(1+|d|)/(2n)$ of $p$. The maps $I+r\,dN$ slide the horizontal rows of the grid by different amounts, hence the name. This is the lattice template for fields whose derivative is a nilpotent shear; no smallness of the shear coefficient $d$ is required, only the radius grows with $|d|$.
--
--   **Formalization Note** Coordinates are `Fin 2 → ℝ`, whose Mathlib norm is the sup norm; the grid is `coordinateGrid n`, defined as $n^{-1}$ times the $\mathbb{Z}$-span of the standard basis, and $N$ is `shearCLM`. The statement is `LatticeModel (d • shearCLM) 1 ((1+|d|)/2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean#L86-L135

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

theorem OAI.RuledApproximation.nilpotent_lattice_model (d : ℝ) :
    LatticeModel (d • shearCLM) 1 ((1+|d|)/2) := by sorry
