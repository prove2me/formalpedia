-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_globalSheet_separation_sq
-- name    : OAI.DoublingHilbert.globalSheet_separation_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:29:26.98098+00:00
-- url     : https://prove2.me/theorems/edcecab8-ca72-4709-b183-bb0a29276350
-- title:
--   Added sheets of two different colors stay $\sqrt{2}\,r_j$ apart under a non-contracting map
-- statement:
--   **Setting.** Let $\ell^2$ be the real Hilbert space of square-summable sequences, with standard unit vectors $e_0,e_1,e_2,\dots$, and write points of the plane as $p=(p_1,p_2)\in\mathbb{R}^2$. Level $j\in\mathbb{N}$ of the construction has scale $r_j=1000^{-(j+1)}$, a number of colors $N_j\ge1$ and a width factor $W_j\ge1$; the displacement of color $i$ at level $j$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is an injective pairing. A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$ and $w_j=i+1$ means color $i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2\in(qr_j,(q+1)r_j)$ for some integer $q$ with $q\bmod N_j=i$ (a horizontal strip) or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$ (a vertical strip). The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ is the open set of all $p$ such that, for every $j$ with $w_j\neq0$, $w_j\le N_j$ and color $w_j-1$ is allowed at level $j$ at $p$. The fixed subset of $\ell^2$ is $S=\{z(p,w):\ p\in\Omega_w\}$, where $z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$.
--
--   Let $E$ be a finite-dimensional real normed space and let $f:S\to E$ be $D$-Lipschitz ($D\ge0$) and non-contracting, that is, $\|f(x)-f(y)\|\ge\|x-y\|$ for all $x,y\in S$. For a tuple $w'$ let $\widetilde F_{w'}:\mathbb{R}^2\to E$ be the fixed globally Lipschitz map that agrees with the sheet $p\mapsto f(z(p,w'))$ on $\Omega_{w'}$, and let $w[j\mapsto k]$ denote the tuple $w$ with its level-$j$ entry replaced by $k$.
--
--   Let $w$ be a tuple and $j$ a level with $w_j=0$, let $i\neq m$ be colors with $i<N_j$ and $m<N_j$, and let $p\in\Omega_w$ be a point at which both color $i$ and color $m$ are allowed at level $j$. Then
--
--   $$
--   \bigl\|\widetilde F_{w[j\mapsto i+1]}(p)-\widetilde F_{w[j\mapsto m+1]}(p)\bigr\|^2\ \ge\ 2\,r_j^2 .
--   $$
--
--   At such a point the two displaced points $z(p,w)+\ell_{j,i}$ and $z(p,w)+\ell_{j,m}$ both belong to $S$ and are $\sqrt2\,r_j$ apart, and the lemma records that the two added sheets keep this separation. Typical such points are crossings, lying in a horizontal strip of color $i$ and in a vertical strip of color $m$. In the finite-dimensional obstruction, such crossings inside one period block yield $N_j$ vectors in a bounded ball of $E$ that are pairwise separated, which is impossible once $N_j$ is large.
--
--   **Formalization Note** The hypotheses on $f$ are `LipschitzWith D f` and `∀ x y, dist x y ≤ dist (f x) (f y)`; the constant $D$ enters only through the chosen extensions `globalSheet hf w'`. The updated tuples are `w.update j (i + 1)` and `w.update j (m + 1)`, and the allowance conditions are `allowed j i p` and `allowed j m p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Grids.lean#L306-L324

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.globalSheet_separation_sq {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ x y, dist x y ≤ dist (f x) (f y))
    (w : Tuple) (j : ℕ) (hj : w j = 0) {i m : ℕ} (him : i ≠ m)
    (hi : i < colors j) (hm : m < colors j) {p : Base} (hp : p ∈ sheetDomain w)
    (hip : allowed j i p) (hmp : allowed j m p) :
    2 * scale j ^ 2 ≤ ‖globalSheet hf (w.update j (i + 1)) p -
      globalSheet hf (w.update j (m + 1)) p‖ ^ 2 := by sorry
