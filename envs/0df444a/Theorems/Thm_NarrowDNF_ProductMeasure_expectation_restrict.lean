-- Prove2me | Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict
-- name    : NarrowDNF.ProductMeasure.expectation_restrict
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:21.476195+00:00
-- url     : https://prove2.me/theorems/a9123d6d-a641-4f4e-9749-3e9bf501bdc0
-- title:
--   Restricting Bernoulli coordinates gives the corresponding product marginal
-- statement:
--   Let $I$ be finite and $A\subseteq I$. For any real $p$, use the finite product weights $w_p(x)=\prod_i(p\text{ if }x_i=1\text{ else }1-p)$. If $F:\{0,1\}^A\to\mathbb R$, then
--   $$
--   \sum_{x\in\{0,1\}^I}w_p(x)F(x|_A)
--   =\sum_{y\in\{0,1\}^A}w_p(y)F(y).
--   $$
--   Thus an observable depending only on $A$ may be averaged on that coordinate set alone. Both empty coordinate sets and arbitrary real $p$ are allowed; in the probability range this is the product marginal law.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L276-L297

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

theorem NarrowDNF.ProductMeasure.expectation_restrict (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : ({i // P i} → Bool) → ℝ) :
    expectation p (fun x : ι → Bool => F (fun i => x i)) = expectation p F := by sorry
