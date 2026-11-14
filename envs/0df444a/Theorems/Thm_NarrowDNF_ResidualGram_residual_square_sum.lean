-- Prove2me | Theorems.Thm_NarrowDNF_ResidualGram_residual_square_sum
-- name    : NarrowDNF.ResidualGram.residual_square_sum
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:51.820931+00:00
-- url     : https://prove2.me/theorems/760e613e-c51f-40b3-b050-599ab8dc71e3
-- title:
--   Exact diagonal and off-diagonal expansion for orthogonal component residuals
-- statement:
--   Let $\Omega$ be finite, $w:\Omega\to\mathbb R$, and $A$ finite. Put $\langle u,v\rangle_w=\sum_xw(x)u(x)v(x)$. Suppose real families $f_i,g_i$ satisfy $\langle f_i,f_j\rangle_w=\langle f_i,g_j\rangle_w=0$ whenever $i,j\in A$ are distinct. Then
--   $$
--   \sum_xw(x)\left(\sum_{i\in A}(f_i(x)-g_i(x))\right)^2
--   =\sum_{i\in A}\sum_xw(x)(f_i(x)-g_i(x))^2
--   +\sum_{i\in A}\sum_{j\in A\setminus\{i\}}\langle g_i,g_j\rangle_w.
--   $$
--   The off-diagonal sum uses ordered pairs. No sign condition on $w$ is needed for this exact algebraic identity.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ResidualGram.lean#L38-L62

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ResidualGram

namespace NarrowDNF.ResidualGram
end NarrowDNF.ResidualGram
open NarrowDNF
open NarrowDNF.ResidualGram
open scoped BigOperators
variable {Ω α : Type*} [Fintype Ω] [DecidableEq α]

theorem NarrowDNF.ResidualGram.residual_square_sum (w : Ω → ℝ) (A : Finset α) (f g : α → Ω → ℝ)
    (hff : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (f j) = 0)
    (hfg : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (g j) = 0) :
    (∑ x, w x * (∑ i ∈ A, (f i x-g i x))^2) =
      (∑ i ∈ A, ∑ x, w x * (f i x-g i x)^2) +
      ∑ i ∈ A, ∑ j ∈ A.erase i, inner w (g i) (g j) := by sorry
