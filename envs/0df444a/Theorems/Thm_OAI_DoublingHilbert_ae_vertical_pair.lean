-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_ae_vertical_pair
-- name    : OAI.DoublingHilbert.ae_vertical_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:32:03.197566+00:00
-- url     : https://prove2.me/theorems/4c4f8565-9bd9-411f-b19c-ae52a1bc787a
-- title:
--   Squared derivative norms of the vertically selected added sheet lie almost everywhere in the closure of all sheet derivative pairs
-- statement:
--   **Setting.** Let $\ell^2$ be the real Hilbert space of square-summable sequences, with standard unit vectors $e_0,e_1,e_2,\dots$, and write points of the plane as $p=(p_1,p_2)\in\mathbb{R}^2$. Level $j\in\mathbb{N}$ of the construction has scale $r_j=1000^{-(j+1)}$, a number of colors $N_j\ge1$ and a width factor $W_j\ge1$; the displacement of color $i$ at level $j$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is an injective pairing. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means color $i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2\in(qr_j,(q+1)r_j)$ for some integer $q$ with $q\bmod N_j=i$ (a horizontal strip) or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$ (a vertical strip). The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ is the open set of all $p$ such that, for every $j$ with $w_j\neq0$, $w_j\le N_j$ and color $w_j-1$ is allowed at level $j$ at $p$. The fixed subset of $\ell^2$ is $S=\{z(p,w):\ p\in\Omega_w\}$, where $z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$.
--
--   Let $E$ be a finite-dimensional real normed space and $f:S\to E$ a $D$-Lipschitz map, $D\ge0$. For a tuple $w'$, the sheet $F_{w'}(p)=f(z(p,w'))$ is defined for $p\in\Omega_{w'}$, and $\widetilde F_{w'}:\mathbb{R}^2\to E$ is a fixed globally Lipschitz map that agrees with $F_{w'}$ on $\Omega_{w'}$ (the global sheet). For a map $g$ on $\mathbb{R}^2$ let $dg(p)$ be its Fréchet derivative at $p$, and write $\partial_1g(p)=dg(p)(1,0)$ and $\partial_2g(p)=dg(p)(0,1)$. Finally $w[j\mapsto k]$ denotes the tuple $w$ with its level-$j$ entry replaced by $k$; when $w_j=0$ and $i<N_j$, the global sheet $\widetilde F_{w[j\mapsto i+1]}$ is the added sheet of color $i$ at level $j$. A point $q$ is good for the tuple $w'$ if $q\in\Omega_{w'}$, $F_{w'}$ is differentiable at $q$, and $q$ is a mean-square Lebesgue point, for averages over closed squares centered at $q$, of both partial derivatives $\partial_1F_{w'}$ and $\partial_2F_{w'}$ extended by zero outside $\Omega_{w'}$. Let $K_f\subseteq\mathbb{R}^2$ be the closure of the set of pairs $\bigl(\|\partial_1F_{w'}(q)\|^2,\|\partial_2F_{w'}(q)\|^2\bigr)$ over all tuples $w'$ and all points $q$ that are good for $w'$; it is a compact set depending only on $f$.
--
--   Fix a tuple $w$, a level $j$ with $w_j=0$, and a rectangle $Q=[x_0,x_1]\times[y_0,y_1]$ with $x_0<x_1$, $y_0<y_1$ and $Q\subseteq\Omega_w$. Let $\kappa_V(p)=\lfloor p_1/(W_jr_j)\rfloor\bmod N_j$ be the color of the vertical strip of width $W_jr_j$ containing $p$, and let $V_k(p)=\partial_k\widetilde F_{w[j\mapsto \kappa_V(p)+1]}(p)$, $k=1,2$, be the partial derivatives of the added sheet selected by this color. Then for almost every $p\in Q$
--
--   $$
--   \bigl(\|V_1(p)\|^2,\ \|V_2(p)\|^2\bigr)\in K_f .
--   $$
--
--   Although the vertically selected field switches between $N_j$ different added sheets, its pair of squared derivative norms takes values, almost everywhere, in the single compact set $K_f$, which depends only on $f$. This is what allows the affine barrier for $K_f$ at its lexicographic maximum to be integrated against the selected fields in the anisotropic energy estimates of the proof that $S$ admits no bi-Lipschitz embedding into any $\mathbb{R}^k$.
--
--   **Formalization Note** The selected fields are `verticalColumn hf w j (1, 0)` and `verticalColumn hf w j (0, 1)`, defined through `stripColor` and `addedSheet`; global sheets are `globalSheet hf w'`, chosen with `Classical.choose`, and derivatives are `fderiv`, equal to $0$ where a map is not differentiable. "Almost every $p\in Q$" refers to the uniform law `Q.law`, the hypothesis $Q\subseteq\Omega_w$ is `Q.closed ⊆ sheetDomain w`, and $K_f$ is `derivativeCompact f`, the closure of `derivativeData f`. The averages in the definition of good points are over closed balls of the maximum metric on the plane, i.e. closed squares.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean#L280-L296

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

theorem OAI.DoublingHilbert.ae_vertical_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ∀ᵐ p ∂Q.law, (‖verticalColumn hf w j (1, 0) p‖ ^ 2,
      ‖verticalColumn hf w j (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by sorry
