-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_verticalColumn_y_mean
-- name    : OAI.DoublingHilbert.verticalColumn_y_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:33:50.853793+00:00
-- url     : https://prove2.me/theorems/0b21afe6-4df1-4cee-9d58-632f1d904c7c
-- title:
--   Mean vertical derivative of the vertically selected added sheet differs from the base sheet's by at most $2Dr_j/(y_1-y_0)$
-- statement:
--   **Setting.** Let $\ell^2$ be the real Hilbert space of square-summable sequences, with standard unit vectors $e_0,e_1,e_2,\dots$, and write points of the plane as $p=(p_1,p_2)\in\mathbb{R}^2$. Level $j\in\mathbb{N}$ of the construction has scale $r_j=1000^{-(j+1)}$, a number of colors $N_j\ge1$ and a width factor $W_j\ge1$; the displacement of color $i$ at level $j$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is an injective pairing. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means color $i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2\in(qr_j,(q+1)r_j)$ for some integer $q$ with $q\bmod N_j=i$ (a horizontal strip) or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$ (a vertical strip). The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ is the open set of all $p$ such that, for every $j$ with $w_j\neq0$, $w_j\le N_j$ and color $w_j-1$ is allowed at level $j$ at $p$. The fixed subset of $\ell^2$ is $S=\{z(p,w):\ p\in\Omega_w\}$, where $z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$.
--
--   Let $E$ be a finite-dimensional real normed space and $f:S\to E$ a $D$-Lipschitz map, $D\ge0$. For a tuple $w'$, $\widetilde F_{w'}:\mathbb{R}^2\to E$ is the fixed globally Lipschitz map that agrees with the sheet $p\mapsto f(z(p,w'))$ on $\Omega_{w'}$, and $w[j\mapsto k]$ denotes the tuple $w$ with its level-$j$ entry replaced by $k$. For a map $g$ on $\mathbb{R}^2$ let $dg(p)$ be its Fréchet derivative at $p$, and write $\partial_1g(p)=dg(p)(1,0)$, $\partial_2g(p)=dg(p)(0,1)$, and $\mathbb{E}_{p\in Q}$ for the mean with respect to the uniform probability measure on a rectangle $Q$.
--
--   Fix a tuple $w$, a level $j$ with $w_j=0$, and a rectangle $Q=[x_0,x_1]\times[y_0,y_1]$ with $x_0<x_1$, $y_0<y_1$ and $Q\subseteq\Omega_w$. Let $\kappa_V(p)=\lfloor p_1/(W_jr_j)\rfloor\bmod N_j$ be the color of the vertical strip of width $W_jr_j$ containing $p$. Then
--
--   $$
--   \Bigl\|\ \mathbb{E}_{p\in Q}\bigl[\partial_2\widetilde F_{w[j\mapsto\kappa_V(p)+1]}(p)\bigr]-\mathbb{E}_{p\in Q}\bigl[\partial_2\widetilde F_w(p)\bigr]\Bigr\|\ \le\ \frac{2D\,r_j}{y_1-y_0}.
--   $$
--
--   Wherever color $i$ is allowed, the added sheet of color $i$ differs from the base sheet $\widetilde F_w$ by at most $Dr_j$, because the corresponding points of $S$ differ by the displacement $\ell_{j,i}$ of length $r_j$. Since the vertical selection is constant along vertical lines, this transfers to the averaged vertical derivative: on rectangles much taller than $r_j$, the vertically selected added sheet and the base sheet have nearly the same mean vertical derivative. This is one of the three mean comparisons feeding the anisotropic energy estimate.
--
--   **Formalization Note** The selected field is `verticalColumn hf w j (0, 1)`, built from `stripColor` and `addedSheet`; $\widetilde F_w$ is `globalSheet hf w`, an extension chosen with `Classical.choose`, and derivatives are `fderiv`, equal to $0$ where a map is not differentiable. The means are integrals against `Q.law`, the height $y_1-y_0$ is `Q.y.length`, and $Q\subseteq\Omega_w$ is `Q.closed ⊆ sheetDomain w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean#L319-L338

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.verticalColumn_y_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (0, 1) p ∂Q.law) -
      (∫ p, column (globalSheet hf w) (0, 1) p ∂Q.law)‖ ≤
      2 * D * scale j / Q.y.length := by sorry
