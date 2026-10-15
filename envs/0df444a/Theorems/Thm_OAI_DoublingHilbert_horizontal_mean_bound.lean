-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_horizontal_mean_bound
-- name    : OAI.DoublingHilbert.horizontal_mean_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:22:20.814332+00:00
-- url     : https://prove2.me/theorems/7c171951-ce70-44cf-856c-342d28fb00d5
-- title:
--   Endpoint control of mean horizontal derivatives for a measurably selected family of Lipschitz maps
-- statement:
--   Let $E$ be a finite-dimensional real normed space. For a map $g:\mathbb{R}^2\to E$ write $\partial_xg(p)=Dg(p)(1,0)$ for its horizontal derivative column (taken to be $0$ where $g$ is not differentiable; for Lipschitz $g$ it exists almost everywhere). Let $Q=[a,b]\times[c,d]$ with $a<b$ and $c<d$, and let $\mu_Q$ be the uniform probability measure on $Q$.
--
--   **Theorem.** Let $\iota$ be a finite index set carrying a $\sigma$-algebra in which all singletons are measurable. Let $F:\mathbb{R}^2\to E$ be Lipschitz, let $G_i:\mathbb{R}^2\to E$ be Lipschitz for each $i\in\iota$ (with arbitrary constants), let $\sigma:\mathbb{R}\to\iota$ be measurable, and let $R\in\mathbb{R}$. Assume that for almost every $y\in[c,d]$ the selected map $G_{\sigma(y)}$ is $R$-close to $F$ at both endpoints of the horizontal segment at height $y$:
--   $$
--   \bigl\|G_{\sigma(y)}(a,y)-F(a,y)\bigr\|\le R\quad\text{and}\quad\bigl\|G_{\sigma(y)}(b,y)-F(b,y)\bigr\|\le R .
--   $$
--   Then the mean horizontal derivative of the row-wise selected maps is close to that of $F$:
--   $$
--   \Bigl\|\int_Q\partial_xG_{\sigma(y)}(x,y)\,d\mu_Q(x,y)-\int_Q\partial_xF(x,y)\,d\mu_Q(x,y)\Bigr\|\le\frac{2R}{b-a}.
--   $$
--
--   This is the transport estimate behind the horizontal energy bound: on each horizontal strip of color $i$ the added sheet $G_i$ differs from the base sheet $F$ by at most a multiple of the strip scale, so the averaged horizontal derivatives differ by that amount divided by the width of $Q$.
--
--   **Formalization Note** The rectangle is a `Rectangle` $Q$ with horizontal segment `Q.x` (endpoints `Q.x.lo` $=a$, `Q.x.hi` $=b$) and vertical segment `Q.y`; $\mu_Q$ is `Q.law`, the product of the normalized Lebesgue measures on $(a,b]$ and $(c,d]$, and "almost every $y$" is with respect to `Q.y.law`. The derivative column is `column g (1, 0) p`. The index type has instances `Fintype`, `MeasurableSpace` and `MeasurableSingletonClass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L235-L269

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

theorem OAI.DoublingHilbert.horizontal_mean_bound {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hleft : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)‖ ≤ R)
    (hright : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.2)) (1, 0) p ∂Q.law) -
      (∫ p, column F (1, 0) p ∂Q.law)‖ ≤ 2 * R / Q.x.length := by sorry
