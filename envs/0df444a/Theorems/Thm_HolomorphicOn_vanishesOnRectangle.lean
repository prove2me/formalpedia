-- Prove2me | Theorems.Thm_HolomorphicOn_vanishesOnRectangle
-- name    : HolomorphicOn.vanishesOnRectangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:33:07.163487+00:00
-- url     : https://prove2.me/theorems/c86b2c23-d3c4-4a9f-8b43-410ba2251a6f
-- title:
--   Cauchy's theorem on rectangles: the rectangle contour integral of a holomorphic function vanishes
-- statement:
--   Let $E$ be a complete normed complex vector space, let $U \subseteq \mathbb{C}$ be a set, and let $f : \mathbb{C} \to E$ be holomorphic on $U$. Let $z, w \in \mathbb{C}$ and suppose the (filled, axis-parallel) rectangle with opposite corners $z$ and $w$ is contained in $U$. Then the contour integral of $f$ around the boundary of that rectangle vanishes:
--   $$\oint_{\partial R(z,w)} f = 0,$$
--   where the rectangle integral is the signed sum of the four side integrals (two horizontal segments at heights $\operatorname{Im} z$ and $\operatorname{Im} w$, and two vertical segments at abscissae $\operatorname{Re} z$ and $\operatorname{Re} w$).
--
--   This is the rectangle form of the Cauchy integral theorem, stated for vector-valued holomorphic maps: holomorphy on a neighborhood of the closed rectangle forces the boundary integral to be zero.
--
--   It is the foundational contour-shifting tool of the PNT+ residue-calculus-on-rectangles library: every deformation of a vertical line of integration (in Perron's formula and in the smoothed Chebyshev contour analysis) is implemented by pasting rectangles on which the integrand is holomorphic and invoking this vanishing theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L103-L108

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by sorry
