-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_residual_orthogonal
-- name    : NarrowDNF.ConditionalExpectation.residual_orthogonal
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:46.567613+00:00
-- url     : https://prove2.me/theorems/1ef24d1d-ed8e-4798-93d7-8de0d6e779f3
-- title:
--   Conditional-expectation residuals are orthogonal to every atom-constant function
-- statement:
--   Let \(A,B\) be finite sets, \(\phi:A\to B\), \(w:A\to(0,\infty)\), and \(F:A\to\mathbb R\). For a realized atom, define its weighted mean and its pullback by
--   $$m(b)=\frac{\sum_{a:\phi(a)=b}w(a)F(a)}{\sum_{a:\phi(a)=b}w(a)},\qquad M(a)=m(\phi(a)).$$
--   Empty atoms have mean zero by convention. For every \(G:B\to\mathbb R\),
--   $$\sum_{a\in A}w(a)(F(a)-M(a))G(\phi(a))=0.$$
--   Weights need not sum to one. This is the finite weighted orthogonality property that characterizes conditional averaging relative to the partition into fibers of \(\phi\).
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L95-L116

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem NarrowDNF.ConditionalExpectation.residual_orthogonal (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 < w a)
    (G : β → ℝ) :
    (∑ a, w a * (F a - conditional φ w F a) * G (φ a)) = 0 := by sorry
