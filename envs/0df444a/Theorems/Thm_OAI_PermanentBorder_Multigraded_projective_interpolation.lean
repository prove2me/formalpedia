-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_projective_interpolation
-- name    : OAI.PermanentBorder.Multigraded.projective_interpolation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:28:28.967471+00:00
-- url     : https://prove2.me/theorems/63bbcdb5-a8c8-432f-8867-b2741dfd7c8c
-- title:
--   Multihomogeneous Lagrange interpolation at distinct points of a product of projective spaces
-- statement:
--   Let $K$ be a field, $\sigma$ a set of variables, $\iota$ a finite set of blocks and $\mathrm{grp}:\sigma\to\iota$. Grade $K[x_\sigma]$ by $\mathbb{Z}^\iota$ with $x_v$ of multidegree $\mathbf e_{\mathrm{grp}(v)}$, and let $R_d$ be the space of multihomogeneous polynomials of multidegree $d\in\mathbb{Z}^\iota$. Call two points $x,y\in K^\sigma$ *block-separated* if there are variables $v,v'$ in the same block, $\mathrm{grp}(v)=\mathrm{grp}(v')$, with
--   $$x_v\,y_{v'}\neq x_{v'}\,y_v,$$
--   i.e. in some block their coordinate vectors are not proportional.
--
--   Let $L$ be a finite set, let $d\in\mathbb{Z}^\iota$ satisfy $d_j\ge|L|$ for every $j\in\iota$, and let $(x_i)_{i\in L}$ be points of $K^\sigma$ that are pairwise block-separated. Suppose that each point has a nonzero coordinate in every block: there are variables $b_{ij}$ ($i\in L$, $j\in\iota$) with $\mathrm{grp}(b_{ij})=j$ and $x_i(b_{ij})\neq0$. Then there are polynomials $p_i\in R_d$ ($i\in L$) with
--   $$p_i(x_k)=\begin{cases}1,&k=i,\\ 0,&k\neq i,\end{cases}\qquad\text{for all}\ i,k\in L .$$
--
--   Thus, in multidegrees at least the number of points, distinct points of a product of projective spaces impose independent conditions on multihomogeneous forms. Consequently, for an ideal vanishing at all the $x_i$, evaluation at the points maps the multidegree-$d$ piece of the quotient onto $K^L$, so the number of such points is at most the dimension of that piece.
--
--   **Formalization Note** $R_d$ is `Piece (blockWeight group) d` and block separation is `BlockSeparated group (x i) (x k)`; the set $\sigma$ need not be finite. The polynomials are evaluated at the given representatives $x_i\in K^\sigma$ themselves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean#L152-L207

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable [Fintype L] [DecidableEq L]

theorem OAI.PermanentBorder.Multigraded.projective_interpolation (group : σ → ι) (d : ι → ℤ)
    (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (hb : ∀ i j, x i (base i j) ≠ 0) :
    ∃ p : L → Piece (K := K) (blockWeight group) d,
      ∀ i j, eval (x j) (p i).val = if j = i then 1 else 0 := by sorry
