-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_separated_family
-- name    : OAI.DoublingHilbert.exists_separated_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:45:32.017811+00:00
-- url     : https://prove2.me/theorems/337f2e79-d638-4315-99eb-1aec2d2f869d
-- title:
--   A non-contracting $D$-Lipschitz map of the constructed set yields arbitrarily large $1$-separated families in the ball of radius $D$
-- statement:
--   **Setting.** Let $\ell^2$ be the Hilbert space of square-summable real sequences, with standard basis $(e_n)_{n\ge0}$. Fix the standard pairing bijection $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. For each level $j\in\mathbb{N}$ let $r_j=1000^{-(j+1)}$, and if $j=\pi(\pi(n,m),k)$ put $N_j=n+1$ (the number of colours) and $W_j=m+1$ (the width factor). A tuple is a finitely supported $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=i+1$ means that colour $i$ is used at level $j$, and $w_j=0$ that level $j$ is unused. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ is *allowed for colour $i$ at level $j$* if $p_2\in(qr_j,(q+1)r_j)$ or $p_1\in(qW_jr_j,(q+1)W_jr_j)$ for some integer $q$ with $q\bmod N_j=i$. The sheet domain $\Omega_w\subseteq\mathbb{R}^2$ consists of the $p$ such that, for every $j$ with $w_j\ne0$, $w_j\le N_j$ and $p$ is allowed for colour $w_j-1$ at level $j$. The constructed set is $S=\{P(p,w): w \text{ a tuple},\ p\in\Omega_w\}\subset\ell^2$, where $P(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne0}r_j\,e_{2+\pi(j,\,w_j-1)}$.
--
--   **Theorem.** Let $E$ be a finite-dimensional real inner product space, let $D\ge0$, and let $f:S\to E$ be a $D$-Lipschitz map that does not contract distances, i.e. $\|p-q\|\le\|f(p)-f(q)\|$ for all $p,q\in S$ (distances in $S$ are those of $\ell^2$). Then for every integer $N\ge1$ there are points $z_1,\dots,z_N\in E$ such that
--
--   $$
--   \|z_i\|\le D\quad\text{for all } i,\qquad\text{and}\qquad \|z_i-z_m\|\ge1\quad\text{for all } i\ne m .
--   $$
--
--   Since a closed ball in a finite-dimensional space is compact, it contains only a bounded number of $1$-separated points, so the theorem implies that no such map $f$ exists. A bi-Lipschitz embedding $g$ of $S$ into a Euclidean space with $a\,\|x-y\|\le|g(x)-g(y)|\le Da\,\|x-y\|$ becomes such a map after division by $a$; this is how bi-Lipschitz embeddings of $S$ into $\mathbb{R}^k$ are excluded for every $k$.
--
--   **Formalization Note** $D$ is a nonnegative real (`NNReal`), the hypothesis is `LipschitzWith D f` together with `dist p q <= dist (f p) (f q)` on the subtype $S$, and the family is indexed by `Fin N`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Crossings.lean#L286-L363

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

theorem OAI.DoublingHilbert.exists_separated_family {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q))
    (N : ℕ) (hN : 0 < N) :
    ∃ z : Fin N → E, (∀ i, ‖z i‖ ≤ D) ∧
      ∀ i m, i ≠ m → 1 ≤ dist (z i) (z m) := by sorry
