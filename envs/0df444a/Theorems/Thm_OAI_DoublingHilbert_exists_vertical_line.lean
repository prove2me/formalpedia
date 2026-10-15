-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_vertical_line
-- name    : OAI.DoublingHilbert.exists_vertical_line
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:43:48.599393+00:00
-- url     : https://prove2.me/theorems/9b177edd-47af-491e-9a5d-976462b3c34a
-- title:
--   A vertical line on which the oscillation of a difference of Lipschitz maps is bounded by the average energy
-- statement:
--   For a closed interval $I=[\alpha,\beta]$ with $\alpha<\beta$ write $|I|=\beta-\alpha$, and for two such intervals $I,J$ let $\mathbb{E}_{I\times J}[e]$ denote the average of $e$ over the rectangle $I\times J$ with respect to the uniform probability measure. For $F:\mathbb{R}^2\to E$ write $\partial_1F(x,y)=DF(x,y)(1,0)$ and $\partial_2F(x,y)=DF(x,y)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable.
--
--   Let $E$ be a finite-dimensional real normed space, let $I=[\alpha_I,\beta_I]$ and $J=[\alpha_J,\beta_J]$ be intervals with $\alpha_I<\beta_I$ and $\alpha_J<\beta_J$, let $F,G:\mathbb{R}^2\to E$ be Lipschitz, let $e:\mathbb{R}^2\to\mathbb{R}$ be bounded and measurable, and let $c\ge0$. Assume that $c\,\|\partial_2G(x,y)-\partial_2F(x,y)\|^2\le e(x,y)$ for every $x\in(\alpha_I,\beta_I)$ and every $y\in\mathbb{R}$. Then there is $x\in(\alpha_I,\beta_I)$ such that for all $a,b\in[\alpha_J,\beta_J]$
--
--   $$
--   c\,\big\|\big(G(x,b)-F(x,b)\big)-\big(G(x,a)-F(x,a)\big)\big\|^2\le|J|^2\,\mathbb{E}_{I\times J}[e] .
--   $$
--
--   This is the vertical counterpart of the horizontal line selection, with the roles of the coordinates exchanged; the vertical line is chosen independently of any horizontal one. The bound holds at every pair of points of the chosen line, which is what allows it to be evaluated at crossing points of selected horizontal and vertical lines.
--
--   **Formalization Note** The intervals are `Segment`s and the average is the integral against `(Rectangle.mk I J).law`, the product of the uniform probability measures on $(\alpha_I,\beta_I]$ and $(\alpha_J,\beta_J]$. Bounded and measurable means `IsBoundedField e` (strongly measurable with a uniform bound); the Lipschitz constants of $F$ and $G$ are arbitrary. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$ (zero where $F$ is not differentiable).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Crossings.lean#L147-L182

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

theorem OAI.DoublingHilbert.exists_vertical_line (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x ∈ Ioo I.lo I.hi, ∀ y : ℝ,
      c * ‖column G (0, 1) (x, y) - column F (0, 1) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ x ∈ Ioo I.lo I.hi, ∀ a ∈ Icc J.lo J.hi, ∀ b ∈ Icc J.lo J.hi,
      c * ‖(G (x, b) - F (x, b)) - (G (x, a) - F (x, a))‖ ^ 2 ≤
        J.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by sorry
