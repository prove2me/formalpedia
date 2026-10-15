-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_color_column
-- name    : OAI.DoublingHilbert.exists_color_column
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:45:09.432133+00:00
-- url     : https://prove2.me/theorems/d27cbea1-d210-4cf6-bde5-572d9165da3a
-- title:
--   In each colour column of a period block, a vertical line along which an added sheet tracks the base sheet
-- statement:
--   **Setting.** Let $\ell^2$ be the Hilbert space of square-summable real sequences, with standard basis $(e_n)_{n\ge0}$. Fix the standard pairing bijection $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. For each level $j\in\mathbb{N}$ let $r_j=1000^{-(j+1)}$, and if $j=\pi(\pi(n,m),k)$ put $N_j=n+1$ (the number of colours) and $W_j=m+1$ (the width factor). A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=i+1$ means that colour $i$ is used at level $j$, and $w_j=0$ that level $j$ is unused. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ is *allowed for colour $i$ at level $j$* if $p_2\in(qr_j,(q+1)r_j)$ or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$. The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ consists of the $p$ such that, for every $j$ with $w_j\ne0$, $w_j\le N_j$ and $p$ is allowed for colour $w_j-1$ at level $j$. The constructed set is $S=\{P(p,w): w \text{ a tuple},\ p\in\Omega_w\}\subset\ell^2$, where $P(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne0}r_j\,e_{2+\pi(j,\,w_j-1)}$.
--
--   Let $E$ be a finite-dimensional real inner product space, let $D\ge0$, and let $f:S\to E$ be $D$-Lipschitz. For a tuple $w$ the sheet $f_w(p)=f(P(p,w))$ is defined for $p\in\Omega_w$, and $F_w:\mathbb{R}^2\to E$ denotes the global sheet, a fixed Lipschitz map that agrees with $f_w$ on $\Omega_w$. For a level $j$ and a colour $i\in\{0,\dots,N_j-1\}$, $F_{w,j,i}$ denotes the global sheet of the tuple obtained from $w$ by setting its $j$-th entry to $i+1$ (colour $i$ added at level $j$). For $F:\mathbb{R}^2\to E$ write $\partial_1F(p)=DF(p)(1,0)$ and $\partial_2F(p)=DF(p)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable. The selected sheets follow the colours of the strips: put $\kappa^h_j(y)=\lfloor y/r_j\rfloor\bmod N_j$ and $\kappa^v_j(x)=\lfloor x/(W_jr_j)\rfloor\bmod N_j$. The horizontal, vertical and combined energy densities at $p=(p_1,p_2)$ are $\mathcal{E}^h_{w,j}(p)=\|\partial_1F_{w,j,\kappa^h_j(p_2)}(p)-\partial_1F_w(p)\|^2$, $\mathcal{E}^v_{w,j}(p)=\|\partial_2F_{w,j,\kappa^v_j(p_1)}(p)-\partial_2F_w(p)\|^2$ and $\mathcal{E}_{w,j}=W_j^2\,\mathcal{E}^h_{w,j}+\mathcal{E}^v_{w,j}$. At level $j$ put $X_j=N_jW_jr_j$ and $Y_j=N_jr_j$. A level-$j$ period block is a rectangle $B=[aX_j,(a+1)X_j]\times[bY_j,(b+1)Y_j]$ with $a,b\in\mathbb{Z}$; its side lengths are $|B_x|=X_j$ and $|B_y|=Y_j$, and $\mathbb{E}_B[g]$ denotes the average of $g$ over $B$ with respect to the uniform probability measure. For $i\in\{0,\dots,N_j-1\}$ the $i$-th row of $B$ is the interval $R_i=[bY_j+ir_j,\,bY_j+(i+1)r_j]$ and its $i$-th column is $C_i=[aX_j+iW_jr_j,\,aX_j+(i+1)W_jr_j]$.
--
--   **Theorem.** In this setting let $w$ be a tuple, $j$ a level, $B$ a level-$j$ period block and $i\in\{0,\dots,N_j-1\}$ a colour. Then there is $x$ in the open column $\big(aX_j+iW_jr_j,\,aX_j+(i+1)W_jr_j\big)$ such that for all $y,y'\in[bY_j,(b+1)Y_j]$
--
--   $$
--   \Big\|\big(F_{w,j,i}(x,y')-F_w(x,y')\big)-\big(F_{w,j,i}(x,y)-F_w(x,y)\big)\Big\|^2\le|B_y|^2\,N_j\,\mathbb{E}_B\big[\mathcal{E}_{w,j}\big].
--   $$
--
--   On the chosen vertical line the displacement $F_{w,j,i}-F_w$ is almost constant across the whole height $|B_y|=N_jr_j$ of the block, with oscillation at most $N_jr_j\sqrt{N_j\,\mathbb{E}_B[\mathcal{E}_{w,j}]}$. No weight appears here because the vertical energy enters the combined energy with coefficient $1$. The column line is chosen independently of the row lines, and the two estimates are later evaluated at the crossing points.
--
--   **Formalization Note** The colour $i$ ranges over `Fin (colors j)` and the block is a `ColorBlock j`. No assumption on $w$ is needed for this estimate. $D$ is a nonnegative real (`NNReal`) and Lipschitz means `LipschitzWith D f` for the subspace distance of $S$. The global sheet is `globalSheet hf w`, a Lipschitz extension chosen by choice; $F_{w,j,i}$ is `addedSheet hf w j i`. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$, which Lean sets to $0$ at points of non-differentiability; the pairing $\pi$ is `Nat.pair`. The average is the integral against `B.rectangle.law`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Crossings.lean#L235-L261

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.exists_color_column {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (B : ColorBlock j)
    (i : Fin (colors j)) :
    ∃ x ∈ Ioo (B.column i).lo (B.column i).hi,
      ∀ a ∈ Icc B.rectangle.y.lo B.rectangle.y.hi,
      ∀ b ∈ Icc B.rectangle.y.lo B.rectangle.y.hi,
        ‖(addedSheet hf w j i (x, b) - globalSheet hf w (x, b)) -
          (addedSheet hf w j i (x, a) - globalSheet hf w (x, a))‖ ^ 2 ≤
        B.rectangle.y.length ^ 2 *
          (colors j * (∫ p, combinedEnergy hf w j p ∂B.rectangle.law)) := by sorry
