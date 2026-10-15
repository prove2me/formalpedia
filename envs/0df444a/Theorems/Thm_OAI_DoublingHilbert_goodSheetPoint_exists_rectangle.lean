-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_goodSheetPoint_exists_rectangle
-- name    : OAI.DoublingHilbert.goodSheetPoint_exists_rectangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:25:14.803655+00:00
-- url     : https://prove2.me/theorems/55236a39-c145-438e-b048-39ca34834505
-- title:
--   Near a good sheet point, small squares make the mean-square derivative error of the extended sheet arbitrarily small
-- statement:
--   **Setting.** Let $\ell^2$ be the real Hilbert space of square-summable sequences, with standard unit vectors $e_0,e_1,e_2,\dots$, and write points of the plane as $p=(p_1,p_2)\in\mathbb{R}^2$. Level $j\in\mathbb{N}$ of the construction has scale $r_j=1000^{-(j+1)}$, a number of colors $N_j\ge1$ and a width factor $W_j\ge1$; the displacement of color $i$ at level $j$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is an injective pairing. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means color $i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2\in(qr_j,(q+1)r_j)$ for some integer $q$ with $q\bmod N_j=i$ (a horizontal strip) or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$ (a vertical strip). The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ is the open set of all $p$ such that, for every $j$ with $w_j\neq0$, $w_j\le N_j$ and color $w_j-1$ is allowed at level $j$ at $p$. The fixed subset of $\ell^2$ is $S=\{z(p,w):\ p\in\Omega_w\}$, where $z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$.
--
--   Let $E$ be a finite-dimensional real normed space and $f:S\to E$ a $D$-Lipschitz map, $D\ge0$. For a tuple $w$, the sheet $F_w(p)=f(z(p,w))$ is defined for $p\in\Omega_w$, and $\widetilde F_w:\mathbb{R}^2\to E$ is a fixed globally Lipschitz map that agrees with $F_w$ on $\Omega_w$. For a map $g$ on $\mathbb{R}^2$ let $dg(p)$ be its Fréchet derivative at $p$, and write $\partial_1g(p)=dg(p)(1,0)$ and $\partial_2g(p)=dg(p)(0,1)$. A point $p$ is a good point of the sheet if $p\in\Omega_w$, $F_w$ is differentiable at $p$, and $p$ is a mean-square Lebesgue point of both partial derivatives extended by zero outside $\Omega_w$: for $k=1,2$,
--   $$\lim_{r\to0^+}\frac{1}{4r^2}\int_{B_r(p)}\bigl\|\mathbf{1}_{\Omega_w}(q)\,\partial_kF_w(q)-\partial_kF_w(p)\bigr\|^2\,dq=0,\qquad B_r(p)=[p_1-r,p_1+r]\times[p_2-r,p_2+r].$$
--
--   Let $p$ be a good point of the sheet $F_w$, put $u=\partial_1F_w(p)$ and $v=\partial_2F_w(p)$, and let $\varepsilon>0$. Then there is a rectangle $Q=[x_0,x_1]\times[y_0,y_1]$ with $x_0<x_1$, $y_0<y_1$ and $Q\subseteq\Omega_w$ such that
--
--   $$
--   \mathbb{E}_{q\in Q}\bigl\|\partial_1\widetilde F_w(q)-u\bigr\|^2<\varepsilon\qquad\text{and}\qquad\mathbb{E}_{q\in Q}\bigl\|\partial_2\widetilde F_w(q)-v\bigr\|^2<\varepsilon ,
--   $$
--
--   where $\mathbb{E}_{q\in Q}$ is the mean with respect to the uniform probability measure on $Q$.
--
--   Near a good point, the derivative of the globally extended sheet is therefore almost constant in mean square, equal to the derivative at $p$, on a genuine rectangle inside the sheet domain. In the proof that $S$ admits no bi-Lipschitz embedding into any $\mathbb{R}^k$, $p$ is chosen so that $(\|u\|^2,\|v\|^2)$ is close to the lexicographic maximum of the compact set of squared derivative norms, and $Q$ is then trimmed to a grid of complete period blocks at a fine level.
--
--   **Formalization Note** The plane carries Lean's product metric, the maximum of the coordinate distances, so the closed balls `Metric.closedBall p r` in the definition `goodSheetPoint f w p` are the squares $B_r(p)$. The derivative fields at $p$ are `sheetColumn (embeddingSheet f w) (sheetDomain w) v p`, which vanish outside $\Omega_w$; $\widetilde F_w$ is `globalSheet hf w`, an extension chosen with `Classical.choose`; derivatives are `fderiv`, equal to $0$ where a map is not differentiable. The means are integrals against `Q.law`, and $Q\subseteq\Omega_w$ is `Q.closed ⊆ sheetDomain w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L380-L406

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

omit [CompleteSpace E] in
theorem OAI.DoublingHilbert.goodSheetPoint_exists_rectangle {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) {w : Tuple} {p : Base} (hp : goodSheetPoint f w p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Rectangle, Q.closed ⊆ sheetDomain w ∧
      (∫ q, ‖column (globalSheet hf w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2 ∂Q.law) < ε ∧
      (∫ q, ‖column (globalSheet hf w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2 ∂Q.law) < ε := by sorry
