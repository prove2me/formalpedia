-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_SupportSeparation_of_bounded
-- name    : OAI.BackwardIntertwiners.SupportSeparation.of_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:27:06.776975+00:00
-- url     : https://prove2.me/theorems/047c1ee6-efd0-43cd-bd54-80d27837d3a6
-- title:
--   Support separation with arbitrary positive constants in the domination bounds
-- statement:
--   Let $w:\mathbb{Z}\to\mathbb{R}$. Say that $w$ has the **support separation property** if for all $b,c:\mathbb{Z}\to\mathbb{C}$, neither identically zero, with $|b_j|\le w(j)$ and $|c_j|\,w(j)\le1$ for all $j\in\mathbb{Z}$ and with $\sum_{j\in\mathbb{Z}}b_jc_{j-r}=0$ for every integer $r\ge1$, there exist integers $t,h$ such that $b_t\neq0$, $c_h\neq0$, $b_j=0$ for all $j>t$, $c_j=0$ for all $j<h$, and $t\le h$.
--
--   **Theorem.** Suppose $w$ has the support separation property. Let $b,c:\mathbb{Z}\to\mathbb{C}$ be sequences, neither identically zero, and let $B,C>0$ be real constants such that
--   $$|b_j|\le B\,w(j),\qquad |c_j|\,w(j)\le C\qquad\text{for all } j\in\mathbb{Z},$$
--   and $\sum_{j\in\mathbb{Z}}b_j\,c_{j-r}=0$ for every integer $r\ge1$. Then there exist integers $t,h$ with
--   $$b_t\neq0,\qquad c_h\neq0,\qquad b_j=0\ \ (j>t),\qquad c_j=0\ \ (j<h),\qquad t\le h .$$
--
--   The definition of the support separation property fixes both constants in the domination bounds to be $1$; this lemma removes that normalization. It is convenient when $b$ and $c$ are built from vectors of arbitrary size, for example the sequences $\overline{z_j}\,w(j)$ and $v_j/w(j)$ obtained from two square-summable sequences $z,v$, which are controlled by the norms of $z$ and $v$ rather than by $1$.
--
--   **Formalization Note** No positivity or monotonicity of $w$ is assumed beyond what the hypothesis `SupportSeparation w` provides. The sums are Lean's `tsum` over `ℤ`, which equals $0$ for non-summable families.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean#L260-L290

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.SupportSeparation.of_bounded {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ t h : ℤ, b t ≠ 0 ∧ c h ≠ 0 ∧
      (∀ j, t < j → b j = 0) ∧ (∀ j, j < h → c j = 0) ∧ t ≤ h := by sorry
