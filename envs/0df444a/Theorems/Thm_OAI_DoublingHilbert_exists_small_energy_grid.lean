-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_small_energy_grid
-- name    : OAI.DoublingHilbert.exists_small_energy_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:41:45.202059+00:00
-- url     : https://prove2.me/theorems/760f3d61-5e16-4936-be51-d38b8fe6fadb
-- title:
--   Period grids of arbitrarily small combined anisotropic energy at levels with any prescribed number of colours
-- statement:
--   **Setting.** Let $\ell^2$ be the Hilbert space of square-summable real sequences, with standard basis $(e_n)_{n\ge0}$. Fix the standard pairing bijection $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. For each level $j\in\mathbb{N}$ let $r_j=1000^{-(j+1)}$, and if $j=\pi(\pi(n,m),k)$ put $N_j=n+1$ (the number of colours) and $W_j=m+1$ (the width factor). A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=i+1$ means that colour $i$ is used at level $j$, and $w_j=0$ that level $j$ is unused. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ is *allowed for colour $i$ at level $j$* if $p_2\in(qr_j,(q+1)r_j)$ or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$. The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ consists of the $p$ such that, for every $j$ with $w_j\ne0$, $w_j\le N_j$ and $p$ is allowed for colour $w_j-1$ at level $j$. The constructed set is $S=\{P(p,w): w \text{ a tuple},\ p\in\Omega_w\}\subset\ell^2$, where $P(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne0}r_j\,e_{2+\pi(j,\,w_j-1)}$.
--
--   Let $E$ be a finite-dimensional real inner product space, let $D\ge0$, and let $f:S\to E$ be $D$-Lipschitz. For a tuple $w$ the sheet $f_w(p)=f(P(p,w))$ is defined for $p\in\Omega_w$, and $F_w:\mathbb{R}^2\to E$ denotes the global sheet, a fixed Lipschitz map that agrees with $f_w$ on $\Omega_w$. For a level $j$ and a colour $i\in\{0,\dots,N_j-1\}$, $F_{w,j,i}$ denotes the global sheet of the tuple obtained from $w$ by setting its $j$-th entry to $i+1$ (colour $i$ added at level $j$). For $F:\mathbb{R}^2\to E$ write $\partial_1F(p)=DF(p)(1,0)$ and $\partial_2F(p)=DF(p)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable. The selected sheets follow the colours of the strips: put $\kappa^h_j(y)=\lfloor y/r_j\rfloor\bmod N_j$ and $\kappa^v_j(x)=\lfloor x/(W_jr_j)\rfloor\bmod N_j$. The horizontal, vertical and combined energy densities at $p=(p_1,p_2)$ are $\mathcal{E}^h_{w,j}(p)=\|\partial_1F_{w,j,\kappa^h_j(p_2)}(p)-\partial_1F_w(p)\|^2$, $\mathcal{E}^v_{w,j}(p)=\|\partial_2F_{w,j,\kappa^v_j(p_1)}(p)-\partial_2F_w(p)\|^2$ and $\mathcal{E}_{w,j}=W_j^2\,\mathcal{E}^h_{w,j}+\mathcal{E}^v_{w,j}$. At level $j$ the horizontal and vertical periods are $X_j=N_jW_jr_j$ and $Y_j=N_jr_j$. A level-$j$ period grid is a closed rectangle $Q=[aX_j,(a+n)X_j]\times[bY_j,(b+m)Y_j]$ with $a,b\in\mathbb{Z}$ and integers $n,m\ge1$; its side lengths are $|Q_x|=nX_j$ and $|Q_y|=mY_j$, and $\mathbb{E}_Q[g]$ denotes the average of a function $g$ over $Q$ with respect to the uniform probability measure.
--
--   **Theorem.** In this setting, for every integer $N\ge1$ and every $\eta>0$ there exist a tuple $w$, a level $j$ with $N_j=N$ and $w_j=0$, and a level-$j$ period grid $Q$ with $Q\subseteq\Omega_w$, such that
--
--   $$
--   \mathbb{E}_Q\big[\mathcal{E}_{w,j}\big]=\mathbb{E}_Q\big[W_j^2\,\mathcal{E}^h_{w,j}+\mathcal{E}^v_{w,j}\big]<\eta .
--   $$
--
--   This is the main analytic output of the non-embeddability argument for the fixed set $S$, valid for every Lipschitz map $f$: on a suitable grid, the derivative along each strip of the sheet obtained by adding that strip's colour is, on average, almost equal to the corresponding derivative of the base sheet. Unlike the number of colours, the width factor $W_j$ of the level is not prescribed. Small combined energy is later used to select, in a single period block, horizontal and vertical lines along which the added sheets stay close to the base sheet.
--
--   **Formalization Note** $D$ is a nonnegative real (`NNReal`) and Lipschitz means `LipschitzWith D f` for the subspace distance of $S$. The global sheet is `globalSheet hf w`, a Lipschitz extension chosen by choice; $F_{w,j,i}$ is `addedSheet hf w j i`. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$, which Lean sets to $0$ at points of non-differentiability; the pairing $\pi$ is `Nat.pair`. The average is the integral against `G.rectangle.law`, the uniform probability measure on the grid.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Energy.lean#L328-L362

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.exists_small_energy_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j), colors j = N ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) < η := by sorry
