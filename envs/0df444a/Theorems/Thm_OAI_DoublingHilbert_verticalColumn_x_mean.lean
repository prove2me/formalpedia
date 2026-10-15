-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_verticalColumn_x_mean
-- name    : OAI.DoublingHilbert.verticalColumn_x_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:35:07.385682+00:00
-- url     : https://prove2.me/theorems/d9a5f354-e2ad-481d-b774-ef7ab8720f27
-- title:
--   On a period grid, the mean horizontal derivative of the vertically selected added sheet is within $2D/W_j$ of the base sheet's
-- statement:
--   **Setting.** Let $\ell^2$ be the real Hilbert space of square-summable sequences, with standard unit vectors $e_0,e_1,e_2,\dots$, and write points of the plane as $p=(p_1,p_2)\in\mathbb{R}^2$. Level $j\in\mathbb{N}$ of the construction has scale $r_j=1000^{-(j+1)}$, a number of colors $N_j\ge1$ and a width factor $W_j\ge1$; the displacement of color $i$ at level $j$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is an injective pairing. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means color $i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2\in(qr_j,(q+1)r_j)$ for some integer $q$ with $q\bmod N_j=i$ (a horizontal strip) or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$ (a vertical strip). The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ is the open set of all $p$ such that, for every $j$ with $w_j\neq0$, $w_j\le N_j$ and color $w_j-1$ is allowed at level $j$ at $p$. The fixed subset of $\ell^2$ is $S=\{z(p,w):\ p\in\Omega_w\}$, where $z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$.
--
--   Let $E$ be a finite-dimensional real normed space and $f:S\to E$ a $D$-Lipschitz map, $D\ge0$. For a tuple $w'$, $\widetilde F_{w'}:\mathbb{R}^2\to E$ is the fixed globally Lipschitz map that agrees with the sheet $p\mapsto f(z(p,w'))$ on $\Omega_{w'}$, and $w[j\mapsto k]$ denotes the tuple $w$ with its level-$j$ entry replaced by $k$. For a map $g$ on $\mathbb{R}^2$ let $dg(p)$ be its Fréchet derivative at $p$, and write $\partial_1g(p)=dg(p)(1,0)$, $\partial_2g(p)=dg(p)(0,1)$, and $\mathbb{E}_{p\in Q}$ for the mean with respect to the uniform probability measure on a rectangle $Q$.
--
--   At level $j$ the strip pattern has horizontal period $X_j=N_jW_jr_j$ and vertical period $Y_j=N_jr_j$. A level-$j$ period grid is a rectangle
--   $$G=[a_xX_j,\,(a_x+n_x)X_j]\times[a_yY_j,\,(a_y+n_y)Y_j]$$
--   with integers $a_x,a_y$ and positive integers $n_x,n_y$. Fix a tuple $w$, a level $j$ with $w_j=0$, and a level-$j$ period grid $G$ with $G\subseteq\Omega_w$, and let $\kappa_V(p)=\lfloor p_1/(W_jr_j)\rfloor\bmod N_j$ be the color of the vertical strip of width $W_jr_j$ containing $p$. Then
--
--   $$
--   \Bigl\|\ \mathbb{E}_{p\in G}\bigl[\partial_1\widetilde F_{w[j\mapsto\kappa_V(p)+1]}(p)\bigr]-\mathbb{E}_{p\in G}\bigl[\partial_1\widetilde F_w(p)\bigr]\Bigr\|\ \le\ \frac{2D}{W_j}.
--   $$
--
--   Here the derivative is taken across the vertical strips that determine the selection, so along each horizontal line the selected map jumps from one added sheet to another, and the endpoint argument can only be run inside single strips of width $W_jr_j$. The resulting error $2Dr_j/(W_jr_j)=2D/W_j$ does not decrease with the size of the grid, but it is small when the width factor $W_j$ is large; for this reason the argument uses fine levels whose width factor is chosen large. This is the third of the mean comparisons feeding the anisotropic energy estimate.
--
--   **Formalization Note** $G$ is a `PeriodGrid j` and the mean is integration against `G.rectangle.law`; the hypothesis $G\subseteq\Omega_w$ is `G.rectangle.closed ⊆ sheetDomain w`. The selected field is `verticalColumn hf w j (1, 0)`, $\widetilde F_w$ is `globalSheet hf w`, and derivatives are `fderiv`, equal to $0$ where a map is not differentiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean#L351-L399

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

theorem OAI.DoublingHilbert.verticalColumn_x_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (1, 0) p ∂G.rectangle.law) -
      (∫ p, column (globalSheet hf w) (1, 0) p ∂G.rectangle.law)‖ ≤
      2 * D / (widthFactor j : ℝ) := by sorry
