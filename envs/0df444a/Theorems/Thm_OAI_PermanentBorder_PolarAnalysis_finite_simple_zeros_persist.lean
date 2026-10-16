-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_finite_simple_zeros_persist
-- name    : OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:54.888384+00:00
-- url     : https://prove2.me/theorems/bf18ecab-c535-47da-89c8-df0c840b4d31
-- title:
--   Finitely many distinct simple zeros persist under small changes of the parameter
-- statement:
--   Let $C$ and $V$ be complex Banach spaces and let $F:C\times V\to V$ be continuously differentiable over $\mathbb{C}$. For a parameter $c\in C$, call a point $x\in V$ *simple* for $F(c,\cdot)$ if the partial derivative of $F$ in the $V$-direction,
--   $$D_VF(c,x):V\to V,\qquad h\longmapsto DF(c,x)(0,h),$$
--   is invertible as a continuous linear map.
--
--   Let $\iota$ be a finite index set, $c\in C$, and let $(x_i)_{i\in\iota}$ be pairwise distinct points of $V$ such that, for every $i$, $F(c,x_i)=0$ and $x_i$ is simple for $F(c,\cdot)$. Then there is a neighbourhood $U$ of $c$ such that for every $c'\in U$ there exist pairwise distinct points $(y_i)_{i\in\iota}$ of $V$ with
--   $$F(c',y_i)=0\quad\text{and}\quad y_i\ \text{simple for}\ F(c',\cdot)\qquad\text{for all}\ i\in\iota .$$
--
--   In other words, the number of distinct simple zeros of $F(c,\cdot)$ cannot drop under small perturbations of the parameter (it is lower semicontinuous in $c$). This is the analytic input for transferring zero counts of polynomial systems from a limit polynomial to the polynomials approximating it, as for border determinants.
--
--   **Formalization Note** Simplicity is `SimpleAt F c x`, i.e. `(fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V).IsInvertible`; differentiability is `ContDiff ℂ 1 F`; the conclusion is an `∀ᶠ c' in 𝓝 c` statement, and pairwise distinctness is `Function.Injective`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/PointBounds.lean#L287-L312

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist {ι : Type*} [Fintype ι]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) {c : C}
    (x : ι → V) (hx : Function.Injective x)
    (hz : ∀ i, F (c,x i) = 0) (hs : ∀ i, SimpleAt F c (x i)) :
    ∀ᶠ c' in 𝓝 c, ∃ y : ι → V, Function.Injective y ∧
      ∀ i, F (c',y i) = 0 ∧ SimpleAt F c' (y i) := by sorry
