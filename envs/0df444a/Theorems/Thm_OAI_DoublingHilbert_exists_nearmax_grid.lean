-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_nearmax_grid
-- name    : OAI.DoublingHilbert.exists_nearmax_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:39:37.007931+00:00
-- url     : https://prove2.me/theorems/b8a10a81-da85-41ef-9289-146eadf6c04b
-- title:
--   Fine period grids on which a base sheet nearly realizes a given point of the derivative set
-- statement:
--   **Setting.** Let $\ell^2$ be the Hilbert space of square-summable real sequences, with standard basis $(e_n)_{n\ge0}$. Fix the standard pairing bijection $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. For each level $j\in\mathbb{N}$ let $r_j=1000^{-(j+1)}$, and if $j=\pi(\pi(n,m),k)$ put $N_j=n+1$ (the number of colours) and $W_j=m+1$ (the width factor). A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=i+1$ means that colour $i$ is used at level $j$, and $w_j=0$ that level $j$ is unused. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ is *allowed for colour $i$ at level $j$* if $p_2\in(qr_j,(q+1)r_j)$ or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$. The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ consists of the $p$ such that, for every $j$ with $w_j\ne0$, $w_j\le N_j$ and $p$ is allowed for colour $w_j-1$ at level $j$. The constructed set is $S=\{P(p,w): w \text{ a tuple},\ p\in\Omega_w\}\subset\ell^2$, where $P(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne0}r_j\,e_{2+\pi(j,\,w_j-1)}$.
--
--   Let $E$ be a finite-dimensional real normed space, let $D\ge0$, and let $f:S\to E$ be $D$-Lipschitz. For a tuple $w$ the sheet $f_w(p)=f(P(p,w))$ is defined for $p\in\Omega_w$, and $F_w:\mathbb{R}^2\to E$ denotes the global sheet, a fixed Lipschitz map that agrees with $f_w$ on $\Omega_w$. For a level $j$ and a colour $i\in\{0,\dots,N_j-1\}$, $F_{w,j,i}$ denotes the global sheet of the tuple obtained from $w$ by setting its $j$-th entry to $i+1$ (colour $i$ added at level $j$). For $F:\mathbb{R}^2\to E$ write $\partial_1F(p)=DF(p)(1,0)$ and $\partial_2F(p)=DF(p)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable. The derivative set $K_f\subseteq\mathbb{R}^2$ is the closure of the set of pairs $(\|\partial_1f_w(p)\|^2,\|\partial_2f_w(p)\|^2)$, where $w$ ranges over all tuples and $p$ over the good points of $f_w$: points of $\Omega_w$ at which $f_w$ is differentiable and which are mean-square Lebesgue points of both partial derivatives of $f_w$ (extended by $0$ outside $\Omega_w$). At level $j$ the horizontal and vertical periods are $X_j=N_jW_jr_j$ and $Y_j=N_jr_j$. A level-$j$ period grid is a closed rectangle $Q=[aX_j,(a+n)X_j]\times[bY_j,(b+m)Y_j]$ with $a,b\in\mathbb{Z}$ and integers $n,m\ge1$; its side lengths are $|Q_x|=nX_j$ and $|Q_y|=mY_j$, and $\mathbb{E}_Q[g]$ denotes the average of a function $g$ over $Q$ with respect to the uniform probability measure.
--
--   **Theorem.** In this setting let $N\ge1$ and $W\ge1$ be integers, let $(A,B)\in K_f$, and let $t>0$. Then there exist a tuple $w$, a level $j$, a level-$j$ period grid $Q$ and vectors $u,v\in E$ such that $N_j=N$, $W_j=W$, $w_j=0$, $Q\subseteq\Omega_w$, $\|u\|\le2D$, $\|v\|\le2D$, and
--
--   $$
--   \begin{gathered}
--   A-\|u\|^2\le t,\qquad B-\|v\|^2\le t,\\
--   \mathbb{E}_Q\big[\|\partial_1F_w-u\|^2\big]\le t^2,\qquad \mathbb{E}_Q\big[\|\partial_2F_w-v\|^2\big]\le t^2,\\
--   \frac{r_j}{|Q_x|}\le t,\qquad \frac{r_j}{|Q_y|}\le t .
--   \end{gathered}
--   $$
--
--   In words: every point of the derivative set is almost realized, in mean square over a whole grid of complete level-$j$ periods, by the partial derivatives of a single base sheet, at an unused level with any prescribed number of colours and width factor, and with the scale $r_j$ as small as desired compared with the grid. These are exactly the hypotheses of the anisotropic energy estimates, which are applied with $(A,B)$ the lexicographic maximum of $K_f$.
--
--   **Formalization Note** Only a normed-space structure on $E$ is used here. $D$ is a nonnegative real (`NNReal`) and Lipschitz means `LipschitzWith D f` for the subspace distance of $S$. The global sheet is `globalSheet hf w`, a Lipschitz extension chosen by choice; $F_{w,j,i}$ is `addedSheet hf w j i`. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$, which Lean sets to $0$ at points of non-differentiability; the pairing $\pi$ is `Nat.pair`. Averages are integrals against `G.rectangle.law`, the product of the uniform probability measures on the sides of the grid.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Energy.lean#L218-L285

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem OAI.DoublingHilbert.exists_nearmax_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N W : ℕ) (hN : 0 < N) (hW : 0 < W)
    {A B : ℝ} (hAB : (A, B) ∈ derivativeCompact f) {t : ℝ} (ht : 0 < t) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j) (u v : E),
      colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      ‖u‖ ≤ 2 * D ∧ ‖v‖ ≤ 2 * D ∧
      A - ‖u‖ ^ 2 ≤ t ∧ B - ‖v‖ ^ 2 ≤ t ∧
      (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      scale j / G.rectangle.x.length ≤ t ∧ scale j / G.rectangle.y.length ≤ t := by sorry
