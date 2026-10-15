-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_source_cover_of_label
-- name    : OAI.DoublingHilbert.source_cover_of_label
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:48:27.583792+00:00
-- url     : https://prove2.me/theorems/9fab9580-5f08-49e1-8746-5929549d19a8
-- title:
--   A labelling of a $t$-ball by at most 300 labels that fixes all levels above $t/64$ yields 76800 half-radius centers
-- statement:
--   Let $\ell^2=\ell^2(\mathbb{N})$ be the real Hilbert space of square-summable real sequences, with standard orthonormal basis $(e_n)_{n\ge 0}$. Fix the scales $s_j=1000^{-(j+1)}$ for $j\in\mathbb{N}$, a pairing bijection $(j,i)\mapsto\langle j,i\rangle$ of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$, and, for each level $j$, two positive integers: a number of colors $N_j$ and a width factor $W_j$ (every pair of positive integers occurs as $(N_j,W_j)$ for infinitely many levels $j$). A base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ determine the point
--
--   $$
--   \Phi(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne 0} s_j\,e_{2+\langle j,\,w_j-1\rangle}\in\ell^2 ,
--   $$
--
--   so an entry $w_j=i+1$ records a displacement of color $i$ at level $j$, and $w_j=0$ records none. The tuple $w$ is admissible at $p$ if for every $j$ with $w_j\ne 0$ one has $w_j\le N_j$ and, for some integer $q$ with $q\equiv w_j-1 \pmod{N_j}$, either $q\,s_j<p_2<(q+1)\,s_j$ (a horizontal strip of width $s_j$) or $q\,W_js_j<p_1<(q+1)\,W_js_j$ (a vertical strip of width $W_js_j$). The fixed set $S\subseteq\ell^2$ consists of all points $\Phi(p,w)$ with $w$ admissible at $p$; it carries the metric $\|y-z\|$ inherited from $\ell^2$.
--
--   For each $z\in S$ fix a representation $z=\Phi(p_z,w_z)$ with $w_z$ admissible at $p_z$ (fixed once and for all by a choice function), and for $x\in S$, $t>0$ write $B_S(x,t)=\{y\in S:\|y-x\|<t\}$.
--
--   Let $x\in S$ and $t>0$, let $L\subseteq\mathbb{N}$ be a finite set with $|L|\le 300$, and let $\lambda:B_S(x,t)\to L$ be a labelling such that points with equal labels have equal tuple entries on every level of scale larger than $t/64$: for all $y,z\in B_S(x,t)$,
--
--   $$
--   \lambda(y)=\lambda(z)\ \Longrightarrow\ (w_y)_j=(w_z)_j\ \text{ for every } j \text{ with } s_j>\frac{t}{64}.
--   $$
--
--   Then there is a finite set $C\subseteq S$ with $|C|\le 76800$ such that every $y\in S$ with $\|y-x\|<t$ satisfies $\|y-c\|<t/2$ for some $c\in C$; that is,
--
--   $$
--   B_S(x,t)\subseteq\bigcup_{c\in C}B_S\Big(c,\frac t2\Big),\qquad |C|\le 76800 .
--   $$
--
--   This reduces the intrinsic doubling property of $S$ (with constant $76800=256\cdot 300$) to the construction, for each ball, of a suitable labelling with at most $300$ labels.
--
--   **Formalization Note** In Lean, $\ell^2$ is `RealL2 = lp (fun _ : ℕ => ℝ) 2`, $S$ is `constructedSet`, $\Phi(p,w)$ is `point p w` with `p : Base = ℝ × ℝ` and `w : Tuple = ℕ →₀ ℕ`, $s_j$ is `scale j`, $N_j$ and $W_j$ are `colors j` and `widthFactor j`, the pairing is `Nat.pair`, and admissibility is `admissible p w`. The representation $(p_z,w_z)$ is `(sourceBase z, sourceTuple z)`, obtained with `Classical.choose`; the labelling is a function from the subtype `Metric.ball x t` of `constructedSet` to the subtype of the finset `labels`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean#L224-L255

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

theorem OAI.DoublingHilbert.source_cover_of_label (x : constructedSet) {t : ℝ} (ht : 0 < t)
    (labels : Finset ℕ) (hcard : labels.card ≤ 300)
    (label : Metric.ball x t → {i // i ∈ labels})
    (hlabel : ∀ y z : Metric.ball x t, label y = label z →
      ∀ j, t / 64 < scale j → sourceTuple y.val j = sourceTuple z.val j) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by sorry
