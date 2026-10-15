-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_constructedSet_cover
-- name    : OAI.DoublingHilbert.constructedSet_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:49:10.084014+00:00
-- url     : https://prove2.me/theorems/ba35eb54-3d84-4103-a022-552fc307e9d0
-- title:
--   The constructed subset of $\ell^2$ is intrinsically doubling with constant 76800
-- statement:
--   Let $\ell^2=\ell^2(\mathbb{N})$ be the real Hilbert space of square-summable real sequences, with standard orthonormal basis $(e_n)_{n\ge 0}$. Fix the scales $s_j=1000^{-(j+1)}$ for $j\in\mathbb{N}$, a pairing bijection $(j,i)\mapsto\langle j,i\rangle$ of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$, and, for each level $j$, two positive integers: a number of colors $N_j$ and a width factor $W_j$ (every pair of positive integers occurs as $(N_j,W_j)$ for infinitely many levels $j$). A base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ determine the point
--
--   $$
--   \Phi(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne 0} s_j\,e_{2+\langle j,\,w_j-1\rangle}\in\ell^2 ,
--   $$
--
--   so an entry $w_j=i+1$ records a displacement of color $i$ at level $j$, and $w_j=0$ records none. The tuple $w$ is admissible at $p$ if for every $j$ with $w_j\ne 0$ one has $w_j\le N_j$ and, for some integer $q$ with $q\equiv w_j-1 \pmod{N_j}$, either $q\,s_j<p_2<(q+1)\,s_j$ (a horizontal strip of width $s_j$) or $q\,W_js_j<p_1<(q+1)\,W_js_j$ (a vertical strip of width $W_js_j$). The fixed set $S\subseteq\ell^2$ consists of all points $\Phi(p,w)$ with $w$ admissible at $p$; it carries the metric $\|y-z\|$ inherited from $\ell^2$.
--
--   Then $S$ is doubling with constant at most $76800$, with centers taken in $S$ itself: for every $x\in S$ and every $t>0$ there is a finite set $C\subseteq S$ with $|C|\le 76800$ such that every $y\in S$ with $\|y-x\|<t$ satisfies $\|y-c\|<t/2$ for some $c\in C$. Writing $B_S(x,t)=\{y\in S:\|y-x\|<t\}$,
--
--   $$
--   \forall x\in S\ \ \forall t>0\ \ \exists\, C\subseteq S \text{ finite},\ |C|\le 76800:\qquad B_S(x,t)\subseteq\bigcup_{c\in C}B_S\Big(c,\frac t2\Big).
--   $$
--
--   This is the doubling half of the main result: the same fixed set $S$ admits no bi-Lipschitz embedding into any finite-dimensional Euclidean space, so the doubling condition alone does not force such an embedding for subsets of Hilbert space.
--
--   **Formalization Note** In Lean, $\ell^2$ is `RealL2 = lp (fun _ : ℕ => ℝ) 2`, $S$ is `constructedSet`, $\Phi(p,w)$ is `point p w` with `p : Base = ℝ × ℝ` and `w : Tuple = ℕ →₀ ℕ`, $s_j$ is `scale j`, $N_j$ and $W_j$ are `colors j` and `widthFactor j`, the pairing is `Nat.pair`, and admissibility is `admissible p w`. Balls are open, distances are those of the subtype `constructedSet`, and the statement is exactly the property `DoublingAtMost constructedSet 76800` unfolded at the point $x$ and radius $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean#L257-L280

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
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric
open Set
open scoped BigOperators

theorem OAI.DoublingHilbert.constructedSet_cover (x : constructedSet) {t : ℝ} (ht : 0 < t) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by sorry
