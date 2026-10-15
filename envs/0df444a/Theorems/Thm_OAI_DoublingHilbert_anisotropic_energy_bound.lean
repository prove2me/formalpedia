-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_anisotropic_energy_bound
-- name    : OAI.DoublingHilbert.anisotropic_energy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:38:49.651525+00:00
-- url     : https://prove2.me/theorems/358627bd-069b-46bc-b940-5cef9ed98b3e
-- title:
--   Anisotropic energy estimates for strip-selected sheets on a near-extremal period grid
-- statement:
--   **Setting.** Let $\ell^2$ be the Hilbert space of square-summable real sequences, with standard basis $(e_n)_{n\ge0}$. Fix the standard pairing bijection $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. For each level $j\in\mathbb{N}$ let $r_j=1000^{-(j+1)}$, and if $j=\pi(\pi(n,m),k)$ put $N_j=n+1$ (the number of colours) and $W_j=m+1$ (the width factor). A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=i+1$ means that colour $i$ is used at level $j$, and $w_j=0$ that level $j$ is unused. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ is *allowed for colour $i$ at level $j$* if $p_2\in(qr_j,(q+1)r_j)$ or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$. The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ consists of the $p$ such that, for every $j$ with $w_j\ne0$, $w_j\le N_j$ and $p$ is allowed for colour $w_j-1$ at level $j$. The constructed set is $S=\{P(p,w): w \text{ a tuple},\ p\in\Omega_w\}\subset\ell^2$, where $P(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne0}r_j\,e_{2+\pi(j,\,w_j-1)}$.
--
--   Let $E$ be a finite-dimensional real inner product space, let $D\ge0$, and let $f:S\to E$ be $D$-Lipschitz. For a tuple $w$ the sheet $f_w(p)=f(P(p,w))$ is defined for $p\in\Omega_w$, and $F_w:\mathbb{R}^2\to E$ denotes the global sheet, a fixed Lipschitz map that agrees with $f_w$ on $\Omega_w$. For a level $j$ and a colour $i\in\{0,\dots,N_j-1\}$, $F_{w,j,i}$ denotes the global sheet of the tuple obtained from $w$ by setting its $j$-th entry to $i+1$ (colour $i$ added at level $j$). For $F:\mathbb{R}^2\to E$ write $\partial_1F(p)=DF(p)(1,0)$ and $\partial_2F(p)=DF(p)(0,1)$ for the partial derivatives, with the convention that they are $0$ where $F$ is not differentiable. The selected sheets follow the colours of the strips: put $\kappa^h_j(y)=\lfloor y/r_j\rfloor\bmod N_j$ and $\kappa^v_j(x)=\lfloor x/(W_jr_j)\rfloor\bmod N_j$. The horizontal, vertical and combined energy densities at $p=(p_1,p_2)$ are $\mathcal{E}^h_{w,j}(p)=\|\partial_1F_{w,j,\kappa^h_j(p_2)}(p)-\partial_1F_w(p)\|^2$, $\mathcal{E}^v_{w,j}(p)=\|\partial_2F_{w,j,\kappa^v_j(p_1)}(p)-\partial_2F_w(p)\|^2$ and $\mathcal{E}_{w,j}=W_j^2\,\mathcal{E}^h_{w,j}+\mathcal{E}^v_{w,j}$.
--
--   The derivative set $K_f\subseteq\mathbb{R}^2$ is the closure of the set of pairs $(\|\partial_1f_w(p)\|^2,\|\partial_2f_w(p)\|^2)$, where $w$ ranges over all tuples and $p$ over the good points of $f_w$: points of $\Omega_w$ at which $f_w$ is differentiable and which are mean-square Lebesgue points of both partial derivatives of $f_w$ (extended by $0$ outside $\Omega_w$). At level $j$ the horizontal and vertical periods are $X_j=N_jW_jr_j$ and $Y_j=N_jr_j$. A level-$j$ period grid is a closed rectangle $Q=[aX_j,(a+n)X_j]\times[bY_j,(b+m)Y_j]$ with $a,b\in\mathbb{Z}$ and integers $n,m\ge1$; its side lengths are $|Q_x|=nX_j$ and $|Q_y|=mY_j$, and $\mathbb{E}_Q[g]$ denotes the average of a function $g$ over $Q$ with respect to the uniform probability measure.
--
--   **Theorem.** In this setting let $w$ be a tuple and $j$ a level with $w_j=0$, and let $Q$ be a level-$j$ period grid with $Q\subseteq\Omega_w$. Let $A,B,C,\varepsilon,t\in\mathbb{R}$ with $C\ge0$ and $0\le t\le1$, and let $u,v\in E$. Assume:
--
--   1. every $z=(z_1,z_2)\in K_f$ satisfies $z_1\le A$ and $z_2\le B+\varepsilon+C(A-z_1)$;
--   2. $\|u\|\le2D$, $\|v\|\le2D$, $A-\|u\|^2\le t$ and $B-\|v\|^2\le t$;
--   3. $\mathbb{E}_Q\big[\|\partial_1F_w-u\|^2\big]\le t^2$ and $\mathbb{E}_Q\big[\|\partial_2F_w-v\|^2\big]\le t^2$;
--   4. $r_j/|Q_x|\le t$ and $r_j/|Q_y|\le t$.
--
--   Then the horizontal and the vertical energy satisfy
--
--   $$
--   \mathbb{E}_Q\big[\mathcal{E}^h_{w,j}\big]\le c_h(D)\,t
--   \qquad\text{and}\qquad
--   \mathbb{E}_Q\big[\mathcal{E}^v_{w,j}\big]\le 2\varepsilon+\frac{16\,C\,D^2}{W_j}+c_v(D,C)\,t,
--   $$
--
--   where $c_h(D)=4+8D(2D+1)$ and $c_v(D,C)=4+2C+8CD+8D(2D+1)$.
--
--   The hypotheses describe a grid on which the base sheet has almost constant partial derivatives $u,v$ whose squared norms almost attain a point $(A,B)$ that is extremal for $K_f$; hypothesis 1 is the affine barrier available at a lexicographic maximum of $K_f$. The conclusion is anisotropic: the horizontal energy is $O(t)$, while the vertical energy also carries the barrier slack $2\varepsilon$ and the term $16CD^2/W_j$ caused by the width $W_jr_j$ of the vertical strips. Because the combined energy weights the horizontal part by $W_j^2$, one first takes $W_j$ large and then $t$ small to make the combined energy as small as desired.
--
--   **Formalization Note** $D$ is a nonnegative real (`NNReal`) and Lipschitz means `LipschitzWith D f` for the subspace distance of $S$. The global sheet is `globalSheet hf w`, a Lipschitz extension chosen by choice; $F_{w,j,i}$ is `addedSheet hf w j i`. Partial derivatives are `column F v p`, the Fréchet derivative `fderiv` of $F$ at $p$ applied to $v$, which Lean sets to $0$ at points of non-differentiability; the pairing $\pi$ is `Nat.pair`. Averages are integrals against `G.rectangle.law`, the product of the uniform probability measures on the two sides of the grid, and the strip colours are computed by `stripColor`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Energy.lean#L125-L205

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

theorem OAI.DoublingHilbert.anisotropic_energy_bound {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w)
    {A B C ε t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : ∀ z ∈ derivativeCompact f, z.1 ≤ A)
    (hbarrier : ∀ z ∈ derivativeCompact f, z.2 ≤ B + ε + C * (A - z.1))
    (u v : E) (hu : ‖u‖ ≤ 2 * D) (hv : ‖v‖ ≤ 2 * D)
    (hnearu : A - ‖u‖ ^ 2 ≤ t) (hnearv : B - ‖v‖ ^ 2 ≤ t)
    (hbaseu : (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hbasev : (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hrx : scale j / G.rectangle.x.length ≤ t)
    (hry : scale j / G.rectangle.y.length ≤ t) :
    (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) ≤ horizontalCoefficient D * t ∧
    (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) ≤
      2 * ε + 16 * C * (D : ℝ) ^ 2 / (widthFactor j : ℝ) + verticalCoefficient D C * t := by sorry
