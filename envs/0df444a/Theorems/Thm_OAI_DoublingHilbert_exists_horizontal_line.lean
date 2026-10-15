-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_horizontal_line
-- name    : OAI.DoublingHilbert.exists_horizontal_line
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:42:47.516759+00:00
-- url     : https://prove2.me/theorems/f1b4e950-e0ce-4e5b-b963-62393ea8b759
-- title:
--   A horizontal line on which the oscillation of a difference of Lipschitz maps is bounded by the average energy
-- statement:
--   For a closed interval $I=[\alpha,\beta]$ with $\alpha<\beta$ write $|I|=\beta-\alpha$, and for two such intervals $I,J$ let $\mathbb{E}_{I\times J}[e]$ denote the average of $e$ over the rectangle $I\times J$ with respect to the uniform probability measure. For $F:\mathbb{R}^2\to E$ write $\partial_1F(x,y)=DF(x,y)(1,0)$ and $\partial_2F(x,y)=DF(x,y)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable.
--
--   Let $E$ be a finite-dimensional real normed space, let $I=[\alpha_I,\beta_I]$ and $J=[\alpha_J,\beta_J]$ be intervals with $\alpha_I<\beta_I$ and $\alpha_J<\beta_J$, let $F,G:\mathbb{R}^2\to E$ be Lipschitz, let $e:\mathbb{R}^2\to\mathbb{R}$ be bounded and measurable, and let $c\ge0$. Assume that $c\,\|\partial_1G(x,y)-\partial_1F(x,y)\|^2\le e(x,y)$ for every $y\in(\alpha_J,\beta_J)$ and every $x\in\mathbb{R}$. Then there is $y\in(\alpha_J,\beta_J)$ such that for all $a,b\in[\alpha_I,\beta_I]$
--
--   $$
--   c\,\big\|\big(G(b,y)-F(b,y)\big)-\big(G(a,y)-F(a,y)\big)\big\|^2\le|I|^2\,\mathbb{E}_{I\times J}[e] .
--   $$
--
--   The conclusion holds at every pair of points of the chosen line, not only for almost every pair, so it can be evaluated at prescribed points such as crossings with other selected lines. Applied to a base sheet and an added sheet, with $e$ the combined energy, it shows that small energy forces the difference of the two sheets to be almost constant along a whole horizontal segment.
--
--   **Formalization Note** The intervals are `Segment`s and the average is the integral against `(Rectangle.mk I J).law`, the product of the uniform probability measures on $(\alpha_I,\beta_I]$ and $(\alpha_J,\beta_J]$. Bounded and measurable means `IsBoundedField e` (strongly measurable with a uniform bound); the Lipschitz constants of $F$ and $G$ are arbitrary. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$ (zero where $F$ is not differentiable).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Crossings.lean#L110-L145

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Metric
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.exists_horizontal_line (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ y ∈ Ioo J.lo J.hi, ∀ x : ℝ,
      c * ‖column G (1, 0) (x, y) - column F (1, 0) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ y ∈ Ioo J.lo J.hi, ∀ a ∈ Icc I.lo I.hi, ∀ b ∈ Icc I.lo I.hi,
      c * ‖(G (b, y) - F (b, y)) - (G (a, y) - F (a, y))‖ ^ 2 ≤
        I.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by sorry
