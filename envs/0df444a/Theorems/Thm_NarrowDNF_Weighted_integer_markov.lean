-- Prove2me | Theorems.Thm_NarrowDNF_Weighted_integer_markov
-- name    : NarrowDNF.Weighted.integer_markov
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:56.56883+00:00
-- url     : https://prove2.me/theorems/c0922074-2de8-4ba5-9590-61d485a47992
-- title:
--   Integer-threshold Markov bound for arbitrary finite nonnegative weights
-- statement:
--   Let $A$ be finite, let $w:A\to[0,\infty)$, let $s:A\to\mathbb N$, and let $c\in\mathbb N$. Then
--   $$
--   \sum_xw(x)\mathbf1_{\{s(x)>c\}}
--   \le\frac{\sum_xw(x)s(x)}{c+1}.
--   $$
--   The weights need not sum to one. The denominator is $c+1$, rather than $c$, because an integer strictly exceeding $c$ is at least $c+1$. In the DNF construction this converts an expected active-set size into a tail bound at an integer certificate-width cutoff.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Weighted.lean#L15-L31

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

theorem NarrowDNF.Weighted.integer_markov (weights : α → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (size : α → ℕ) (cutoff : ℕ) :
    (∑ x, weights x * (if cutoff < size x then 1 else 0)) ≤
      (∑ x, weights x * (size x : ℝ)) / (cutoff + 1 : ℝ) := by sorry
