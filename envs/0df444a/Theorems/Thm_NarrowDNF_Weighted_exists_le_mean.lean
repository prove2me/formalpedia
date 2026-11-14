-- Prove2me | Theorems.Thm_NarrowDNF_Weighted_exists_le_mean
-- name    : NarrowDNF.Weighted.exists_le_mean
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:54.402574+00:00
-- url     : https://prove2.me/theorems/922b33fc-edcb-46e5-9ad8-59bec8f73d8a
-- title:
--   A finite strictly positive probability average has a realization at most its mean
-- statement:
--   Let $A$ be a nonempty finite set, let $w:A\to\mathbb R$ satisfy $w(x)>0$ for every $x$ and $\sum_xw(x)=1$, and let $V:A\to\mathbb R$ be arbitrary. Then
--   $$
--   \exists x\in A:\quad V(x)\le\sum_{y\in A}w(y)V(y).
--   $$
--   There is no nonnegativity condition on $V$. This finite averaging principle selects a deterministic realization from the random choices used by the approximation construction.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Weighted.lean#L33-L50

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Weighted
end NarrowDNF.Weighted
open NarrowDNF
open NarrowDNF
open NarrowDNF.Weighted
open scoped BigOperators
variable {α : Type*} [Fintype α]

theorem NarrowDNF.Weighted.exists_le_mean [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1) (value : α → ℝ) :
    ∃ x, value x ≤ ∑ y, weights y * value y := by sorry
