-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_SupportSeparation_strict_order
-- name    : OAI.BackwardIntertwiners.SupportSeparation.strict_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:28:30.801523+00:00
-- url     : https://prove2.me/theorems/3cdd6c1a-db26-4b2e-bf7f-9ff0b9824828
-- title:
--   Strict ordering of supports when the zeroth correlation also vanishes
-- statement:
--   Let $w:\mathbb{Z}\to\mathbb{R}$ have the **support separation property**: for all $b,c:\mathbb{Z}\to\mathbb{C}$, neither identically zero, with $|b_j|\le w(j)$ and $|c_j|\,w(j)\le1$ for all $j\in\mathbb{Z}$ and with $\sum_{j\in\mathbb{Z}}b_jc_{j-r}=0$ for every integer $r\ge1$, there exist integers $t,h$ such that $b_t\neq0$, $c_h\neq0$, $b_j=0$ for all $j>t$, $c_j=0$ for all $j<h$, and $t\le h$.
--
--   **Theorem.** Let $b,c:\mathbb{Z}\to\mathbb{C}$ be sequences, neither identically zero, and let $B,C>0$ be real numbers with $|b_k|\le B\,w(k)$ and $|c_k|\,w(k)\le C$ for all $k\in\mathbb{Z}$. Suppose that the correlations vanish for every $r\in\mathbb{N}$, including $r=0$:
--   $$\sum_{k\in\mathbb{Z}} b_k\,c_{k-r}=0\qquad(r=0,1,2,\dots).$$
--   Then every index in the support of $b$ is strictly smaller than every index in the support of $c$: for all integers $i,j$,
--   $$b_i\neq0\ \text{ and }\ c_j\neq0\quad\Longrightarrow\quad i<j .$$
--
--   The extra identity at $r=0$ upgrades the weak ordering $t\le h$ of the support separation property to a strict one. This is the form needed when the identities express orthogonality of a vector to all powers $T^r v$, $r\ge0$, of a weighted shift $T$ applied to another vector $v$ (the case $r=0$ being orthogonality to $v$ itself); it then says that the two vectors have strictly separated supports.
--
--   **Formalization Note** The sums are `tsum`s over `ℤ` (equal to $0$ for non-summable families), and $r$ ranges over `ℕ` with no lower bound. The hypotheses that $b$ and $c$ are not identically zero are stated separately from the hypotheses `b i ≠ 0` and `c j ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/FiberTails.lean#L49-L72

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.SupportSeparation.strict_order {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, (∑' j : ℤ, b j * c (j-r)) = 0)
    {i j : ℤ} (hbi : b i ≠ 0) (hcj : c j ≠ 0) : i < j := by sorry
