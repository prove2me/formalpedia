-- Prove2me | Theorems.Thm_OAI_FiniteCircle_row_separation
-- name    : OAI.FiniteCircle.row_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:26:22.626257+00:00
-- url     : https://prove2.me/theorems/d4789ed1-b7d8-4ba5-98fd-7b22125c8b8e
-- title:
--   Row-by-row separation of position-tagged words gives a global deficit lower bound
-- statement:
--   For words $u,v$ let $\operatorname{lcs}(u,v)$ be the length of a longest common subsequence and $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ the deficit. For a word $x=x_0x_1\cdots$ and $p,\ell\in\mathbb{N}$, $x[p,p+\ell)$ denotes the segment $x_p\cdots x_{p+\ell-1}$.
--
--   Let $\beta$ be an alphabet and $N,t,L\in\mathbb{N}$ with $L\ge1$ and $t\ge4$, and put $W=tL$. Let $x,y$ be words over $\beta$ with $|x|=|y|=WN$, viewed as $N$ rows $X_i=x[iW,(i+1)W)$ and $Y_j=y[jW,(j+1)W)$ of length $W$, each row consisting of $t$ consecutive blocks of length $L$. Assume that the letters record the index of their block within the row: there is a map $\operatorname{tag}:\beta\to\mathbb{N}$ with
--   $$
--   \operatorname{tag}(x_k)=\lfloor k/L\rfloor\bmod t\quad(0\le k<|x|),\qquad \operatorname{tag}(y_k)=\lfloor k/L\rfloor\bmod t\quad(0\le k<|y|).
--   $$
--   Let $\rho\in\mathbb{R}$ with $\rho\le\tfrac12$, and assume that every row of $x$ is far from every row of $y$:
--   $$
--   \operatorname{def}(X_i,Y_j)\ge\rho\,tL\qquad\text{for all } 0\le i,j<N .
--   $$
--
--   **Theorem.** Under these hypotheses
--   $$
--   \operatorname{def}(x,y)\ge\frac{\rho}{2}\,|x| .
--   $$
--
--   This is a local-to-global principle for the deficit: two concatenations of rows are, relative to their length, at least half as far apart as the closest pair of rows, provided the letters carry their block index, which prevents a common subsequence from spreading one row of $x$ cheaply over several rows of $y$. It is used to propagate separation bounds from one level of the recursive hard-word constructions to the next. No lower bound on $\rho$ is assumed (for $\rho\le0$ the statement is trivial).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean#L253-L294

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.row_separation {β : Type*} {x y : List β} {N t L : ℕ} (hL : 0 < L) (ht : 4 ≤ t)
    (hx : x.length = (t*L)*N) (hy : y.length = (t*L)*N)
    (tag : β → ℕ)
    (htagx : ∀ k : Fin x.length, tag (x.get k) = (k.val/L)%t)
    (htagy : ∀ k : Fin y.length, tag (y.get k) = (k.val/L)%t)
    (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hrows : ∀ i j : Fin N, ρ*(t*L) ≤
      (deficit (segment x (i.val*(t*L)) (t*L)) (segment y (j.val*(t*L)) (t*L)) : ℝ)) :
    ρ/2 * x.length ≤ (deficit x y : ℝ) := by sorry
