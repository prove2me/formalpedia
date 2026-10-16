-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_component_finrank_le_one_of_linear_relations
-- name    : OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:25:00.848087+00:00
-- url     : https://prove2.me/theorems/b042c792-31e4-4e3b-ae2b-99580053b703
-- title:
--   Multigraded pieces have dimension at most one when each variable is proportional to a block representative
-- statement:
--   Let $K$ be a field, $\sigma$ a finite set of variables, $\iota$ a finite set of blocks and $\mathrm{grp}:\sigma\to\iota$ an assignment of variables to blocks. Grade $R=K[x_\sigma]$ by $\mathbb{Z}^\iota$, giving $x_v$ the multidegree $\mathbf e_{\mathrm{grp}(v)}$ (the unit vector of its block); thus $x^m$ has multidegree $\bigl(\sum_{v:\,\mathrm{grp}(v)=j}m_v\bigr)_{j\in\iota}$. For $d\in\mathbb{Z}^\iota$ let $R_d$ be the space of polynomials that are multihomogeneous of multidegree $d$, and for an ideal $I$ put $Q_d(I)=R_d/(I\cap R_d)$.
--
--   Let $I\subseteq R$ be an ideal, $(z_j)_{j\in\iota}$ polynomials in $R$ and $(c_v)_{v\in\sigma}$ scalars in $K$ such that
--   $$x_v-c_v\,z_{\mathrm{grp}(v)}\in I\qquad\text{for every }v\in\sigma .$$
--   Then $\dim_KQ_d(I)\le1$ for every $d\in\mathbb{Z}^\iota$.
--
--   In words: if modulo $I$ every variable of block $j$ is a scalar multiple of one common element $z_j$, then each multigraded piece of the quotient is at most one-dimensional. Neither $I$ nor the $z_j$ need be homogeneous. This is the bound used in the balanced case of a multihomogeneous Bézout-type count, where the linear forms in $I$ have codimension at most one in every block.
--
--   **Formalization Note** The multigrading is the weight `blockWeight group`, sending $v$ to `Pi.single (group v) 1` in `ι → ℤ`; $Q_d(I)$ is `componentQuotient (blockWeight group) I d` and the dimension is `Module.finrank K` (these pieces are finite-dimensional since $\sigma$ is finite). For $d$ with a negative entry, $R_d=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Multigraded.lean#L301-L354

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

theorem OAI.PermanentBorder.Multigraded.component_finrank_le_one_of_linear_relations (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (z : ι → MvPolynomial σ K) (c : σ → K)
    (hrel : ∀ v, X v - C (c v) * z (group v) ∈ I) (d : ι → ℤ) :
    Module.finrank K (componentQuotient (blockWeight group) I d) ≤ 1 := by sorry
