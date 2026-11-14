-- Prove2me | Theorems.Thm_NarrowDNF_ProductMeasure_sum_prod_two_coordinates
-- name    : NarrowDNF.ProductMeasure.sum_prod_two_coordinates
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:20.794197+00:00
-- url     : https://prove2.me/theorems/559e1c9b-bd2a-4ec0-88fc-f5f7289b2cf8
-- title:
--   Double cube sums factor into independent two-bit coordinate sums
-- statement:
--   For a finite coordinate set $I$ and any real-valued family $F_i:\{0,1\}^2\to\mathbb R$,
--   $$
--   \sum_{x,y\in\{0,1\}^I}\prod_{i\in I}F_i(x_i,y_i)
--   =\prod_{i\in I}\left(\sum_{a,b\in\{0,1\}}F_i(a,b)\right).
--   $$
--   No positivity or probability normalization is required. The identity also includes the empty coordinate set. It supplies the finite distributivity step that converts the point-mass calculation for coordinatewise forcing into separate computations on individual bits.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L190-L205

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
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.ProductMeasure.sum_prod_two_coordinates (F : ι → Bool → Bool → ℝ) :
    (∑ x : ι → Bool, ∑ y : ι → Bool, ∏ i, F i (x i) (y i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, F i a b := by sorry
