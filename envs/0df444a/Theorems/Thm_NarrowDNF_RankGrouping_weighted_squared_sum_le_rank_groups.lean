-- Prove2me | Theorems.Thm_NarrowDNF_RankGrouping_weighted_squared_sum_le_rank_groups
-- name    : NarrowDNF.RankGrouping.weighted_squared_sum_le_rank_groups
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:51.496269+00:00
-- url     : https://prove2.me/theorems/d32445cc-1f65-42dc-ba2e-0dbead42a08a
-- title:
--   Weighted Cauchy–Schwarz after grouping by rank
-- statement:
--   Let $\Omega$ be finite with weights $w(x)\ge0$. Let $A,R$ be finite sets and $r:A\to R$ a rank assignment; equivalently, every index in $A$ has its rank in $R$. For arbitrary real values $v(x,i)$,
--   $$
--   \sum_xw(x)\left(\sum_{i\in A}v(x,i)\right)^2
--   \le |R|\sum_{s\in R}\sum_xw(x)
--   \left(\sum_{i\in A:r(i)=s}v(x,i)\right)^2.
--   $$
--   There is no normalization assumption on $w$. Taking the rank set to be $1,\ldots,k$ gives the factor $k$; allowing rank zero also gives the factor $k+1$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/RankGrouping.lean#L25-L43

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.RankGrouping
end NarrowDNF.RankGrouping
open NarrowDNF
open NarrowDNF.RankGrouping
open scoped BigOperators
variable {α β : Type*} [DecidableEq β]

theorem NarrowDNF.RankGrouping.weighted_squared_sum_le_rank_groups {Ω : Type*} [Fintype Ω]
    (weights : Ω → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : Ω → α → ℝ) :
    (∑ x, weights x * (∑ i ∈ A, v x i)^2) ≤ (R.card : ℝ) *
      ∑ r ∈ R, ∑ x, weights x * (∑ i ∈ A with rank i = r, v x i)^2 := by sorry
