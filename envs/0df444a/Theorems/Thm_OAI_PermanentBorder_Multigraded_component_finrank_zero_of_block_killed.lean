-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_component_finrank_zero_of_block_killed
-- name    : OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:25:31.509764+00:00
-- url     : https://prove2.me/theorems/d0e59c93-1b67-4a2f-8c76-8e0d66990003
-- title:
--   A multigraded piece vanishes when the ideal contains all variables of a block of positive degree
-- statement:
--   Let $K$ be a field, $\sigma$ a finite set of variables, $\iota$ a finite set of blocks and $\mathrm{grp}:\sigma\to\iota$. Grade $R=K[x_\sigma]$ by $\mathbb{Z}^\iota$ with $x_v$ of multidegree $\mathbf e_{\mathrm{grp}(v)}$, let $R_d$ be the space of multihomogeneous polynomials of multidegree $d\in\mathbb{Z}^\iota$, and put $Q_d(I)=R_d/(I\cap R_d)$ for an ideal $I$.
--
--   Let $I\subseteq R$ be an ideal and $j\in\iota$ a block such that $x_v\in I$ for every variable $v$ with $\mathrm{grp}(v)=j$. Then for every $d\in\mathbb{Z}^\iota$ with $d_j>0$,
--   $$\dim_KQ_d(I)=0,$$
--   that is, $R_d\subseteq I$.
--
--   Geometrically, the equations in $I$ have no common zero in the $j$-th projective factor, and correspondingly every multigraded piece of positive degree in that block is killed. This is the bound used in the unbalanced case of a multihomogeneous Bézout-type count.
--
--   **Formalization Note** The grading is `blockWeight group` and $Q_d(I)$ is `componentQuotient (blockWeight group) I d`; the conclusion is `Module.finrank K (componentQuotient (blockWeight group) I d) = 0`, which for these finite-dimensional pieces means the quotient is zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Multigraded.lean#L356-L389

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

theorem OAI.PermanentBorder.Multigraded.component_finrank_zero_of_block_killed (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (j : ι)
    (hkill : ∀ v, group v = j → X v ∈ I) (d : ι → ℤ) (hd : 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight group) I d) = 0 := by sorry
