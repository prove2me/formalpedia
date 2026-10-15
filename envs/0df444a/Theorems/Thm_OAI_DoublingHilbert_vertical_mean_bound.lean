-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_vertical_mean_bound
-- name    : OAI.DoublingHilbert.vertical_mean_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:23:03.469791+00:00
-- url     : https://prove2.me/theorems/1da9be8b-8096-41ad-9a82-844c5c6ba5fe
-- title:
--   Endpoint transport for the mean vertical derivative of a column-wise selected Lipschitz map
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $Q=[x_0,x_1]\times[y_0,y_1]$ be a rectangle with $x_0<x_1$ and $y_0<y_1$. Write $\mathbb{E}_{p\in Q}$ for the mean with respect to the uniform probability measure on $Q$, and for a map $g:\mathbb{R}^2\to E$ with Fréchet derivative $dg(p)$ at $p$ let $\partial_2g(p)=dg(p)(0,1)$ be its vertical partial derivative.
--
--   Let $\iota$ be a finite index set, let $F:\mathbb{R}^2\to E$ be Lipschitz and let $G_i:\mathbb{R}^2\to E$, $i\in\iota$, be Lipschitz maps. Let $\sigma:\mathbb{R}\to\iota$ be measurable; it selects the map $G_{\sigma(x)}$ used on the vertical line through $(x,0)$. Let $R\in\mathbb{R}$ and assume that on the bottom and top edges of $Q$ the selected map is $R$-close to $F$: for almost every $x\in[x_0,x_1]$,
--   $$\|G_{\sigma(x)}(x,y_0)-F(x,y_0)\|\le R\qquad\text{and}\qquad\|G_{\sigma(x)}(x,y_1)-F(x,y_1)\|\le R .$$
--   Then
--
--   $$
--   \Bigl\|\ \mathbb{E}_{p\in Q}\bigl[\partial_2G_{\sigma(p_1)}(p)\bigr]-\mathbb{E}_{p\in Q}\bigl[\partial_2F(p)\bigr]\Bigr\|\ \le\ \frac{2R}{y_1-y_0}.
--   $$
--
--   When the selection is constant along vertical lines, the mean vertical derivative of the selected field is therefore determined by the values on the bottom and top edges, up to an error $2R$ divided by the height. This is the vertical counterpart of the horizontal endpoint transport bound; in the construction of a doubling subset of $\ell^2$ without bi-Lipschitz embeddings into $\mathbb{R}^k$ it is applied to the vertically selected added sheets, with $R$ the size of the displacement between an added sheet and the base sheet.
--
--   **Formalization Note** The mean is integration against `Q.law`, the product of the normalized Lebesgue measures on $(x_0,x_1]$ and $(y_0,y_1]$, and "almost every $x$" refers to the uniform law `Q.x.law` of the bottom side. The derivative field is `column G (0, 1) p`, i.e. `fderiv ℝ G p (0, 1)`, which is $0$ where the map is not differentiable (a null set, by Rademacher's theorem). The index type carries a measurable structure with measurable singletons; the Lipschitz constants of $F$ and the $G_i$ are arbitrary and do not enter the bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L271-L305

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.vertical_mean_bound {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hbottom : ∀ᵐ x ∂Q.x.law, ‖G (σ x) (x, Q.y.lo) - F (x, Q.y.lo)‖ ≤ R)
    (htop : ∀ᵐ x ∂Q.x.law, ‖G (σ x) (x, Q.y.hi) - F (x, Q.y.hi)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (0, 1) p ∂Q.law) -
      (∫ p, column F (0, 1) p ∂Q.law)‖ ≤ 2 * R / Q.y.length := by sorry
