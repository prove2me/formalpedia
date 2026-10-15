-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_horizontal_mean_bound_stripes
-- name    : OAI.DoublingHilbert.horizontal_mean_bound_stripes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:29:50.361461+00:00
-- url     : https://prove2.me/theorems/32c13745-d83b-4e1c-91b3-9280b686501b
-- title:
--   Strip-by-strip endpoint transport for horizontal derivatives of a column-wise selected map
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\iota$ a finite index set, $F:\mathbb{R}^2\to E$ a Lipschitz map and $G_i:\mathbb{R}^2\to E$, $i\in\iota$, Lipschitz maps; for a map $g$ with Fréchet derivative $dg(p)$ at $p$ write $\partial_1g(p)=dg(p)(1,0)$ for the horizontal partial derivative. Fix $a\in\mathbb{R}$, a strip width $h>0$, an integer $n\ge1$ and an interval $[y_0,y_1]$ with $y_0<y_1$, and let
--   $$Q=[a,a+nh]\times[y_0,y_1]$$
--   be the union of the $n$ vertical strips $[a+kh,a+(k+1)h]\times[y_0,y_1]$, $k=0,\dots,n-1$. Let $\sigma:\mathbb{R}\to\iota$ be measurable, let $c_0,\dots,c_{n-1}\in\iota$ and $R\in\mathbb{R}$, and assume that for every $k$:
--
--   1. $\sigma(x)=c_k$ for every $x$ in the open cell $(a+kh,\,a+(k+1)h)$;
--   2. $\|G_{c_k}(x,y)-F(x,y)\|\le R$ for every $x\in(a+kh,\,a+(k+1)h)$ and every $y\in(y_0,y_1)$.
--
--   Then, with $\mathbb{E}_{p\in Q}$ the mean with respect to the uniform probability measure on $Q$,
--
--   $$
--   \Bigl\|\ \mathbb{E}_{p\in Q}\bigl[\partial_1G_{\sigma(p_1)}(p)\bigr]-\mathbb{E}_{p\in Q}\bigl[\partial_1F(p)\bigr]\Bigr\|\ \le\ \frac{2R}{h}.
--   $$
--
--   Here the selection depends on the horizontal coordinate, so the selected map $p\mapsto G_{\sigma(p_1)}(p)$ may jump across strip boundaries and cannot be integrated horizontally across the whole rectangle; the estimate is obtained strip by strip, and only the strip width $h$, not the total width $nh$, enters the bound. In the doubling-subset construction it controls the horizontal derivative of the vertically selected added sheets, whose strips have width $W_jr_j$.
--
--   **Formalization Note** The rectangle is `Rectangle.mk (Segment.grid a h n hh hn) J`, with `J` the segment $[y_0,y_1]$, and the cells are `Segment.cell a h hh k`; the mean is integration against its uniform law. The derivative field is `column G (1, 0) p`, i.e. `fderiv`, which is $0$ where the map is not differentiable. The index type carries a measurable structure with measurable singletons, and the Lipschitz constants are arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean#L38-L93

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.horizontal_mean_bound_stripes {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {F : Base → E} {G : ι → Base → E}
    {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) (c : Fin n → ι) {R : ℝ}
    (hcolor : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, σ x = c i)
    (hbound : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, ∀ y ∈ Ioo J.lo J.hi, ‖G (c i) (x, y) - F (x, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) -
      (∫ p, column F (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law)‖ ≤
      2 * R / h := by sorry
