-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_no_scaled_embedding
-- name    : OAI.DoublingHilbert.no_scaled_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:50:53.607399+00:00
-- url     : https://prove2.me/theorems/d5dfacee-03d0-4270-b38d-6eff5319b679
-- title:
--   The constructed subset of $\ell^2$ has no bi-Lipschitz embedding into a finite-dimensional inner product space
-- statement:
--   Let $\ell^2=\ell^2(\mathbb{N})$ be the real Hilbert space of square-summable real sequences, with standard orthonormal basis $(e_n)_{n\ge 0}$. Fix the scales $s_j=1000^{-(j+1)}$ for $j\in\mathbb{N}$, a pairing bijection $(j,i)\mapsto\langle j,i\rangle$ of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$, and, for each level $j$, two positive integers: a number of colors $N_j$ and a width factor $W_j$ (every pair of positive integers occurs as $(N_j,W_j)$ for infinitely many levels $j$). A base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ determine the point
--
--   $$
--   \Phi(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne 0} s_j\,e_{2+\langle j,\,w_j-1\rangle}\in\ell^2 ,
--   $$
--
--   so an entry $w_j=i+1$ records a displacement of color $i$ at level $j$, and $w_j=0$ records none. The tuple $w$ is admissible at $p$ if for every $j$ with $w_j\ne 0$ one has $w_j\le N_j$ and, for some integer $q$ with $q\equiv w_j-1 \pmod{N_j}$, either $q\,s_j<p_2<(q+1)\,s_j$ (a horizontal strip of width $s_j$) or $q\,W_js_j<p_1<(q+1)\,W_js_j$ (a vertical strip of width $W_js_j$). The fixed set $S\subseteq\ell^2$ consists of all points $\Phi(p,w)$ with $w$ admissible at $p$; it carries the metric $\|y-z\|$ inherited from $\ell^2$.
--
--   Let $E$ be a finite-dimensional real inner product space. Then there is no map $f:S\to E$ for which there exist a scale $a>0$ and a distortion $D\ge 1$ such that
--
--   $$
--   a\,\|x-y\|\le\|f(x)-f(y)\|\le D\,a\,\|x-y\|\qquad\text{for all } x,y\in S .
--   $$
--
--   In other words, $S$ admits no bi-Lipschitz embedding into any finite-dimensional Euclidean space, whatever the distortion and whatever the change of scale. This is the nonembedding half of the main result; together with the intrinsic doubling bound $76800$ for the same set $S$, it shows that a doubling subset of Hilbert space need not bi-Lipschitz embed into any $\mathbb{R}^k$.
--
--   **Formalization Note** In Lean, $\ell^2$ is `RealL2 = lp (fun _ : ℕ => ℝ) 2`, $S$ is `constructedSet`, $\Phi(p,w)$ is `point p w` with `p : Base = ℝ × ℝ` and `w : Tuple = ℕ →₀ ℕ`, $s_j$ is `scale j`, $N_j$ and $W_j$ are `colors j` and `widthFactor j`, the pairing is `Nat.pair`, and admissibility is `admissible p w`. The space $E$ carries the instances `NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `CompleteSpace E` and `FiniteDimensional ℝ E`, and the theorem concludes `False` from the existence of $f$, $a$, $D$ with the stated properties; the main theorem uses it with $E$ = `EuclideanSpace ℝ (Fin k)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Main.lean#L28-L49

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
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem OAI.DoublingHilbert.no_scaled_embedding (f : constructedSet → E) {a D : ℝ}
    (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) : False := by sorry
