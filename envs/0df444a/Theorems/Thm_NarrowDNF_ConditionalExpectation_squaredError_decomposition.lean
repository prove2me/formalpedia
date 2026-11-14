-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_squaredError_decomposition
-- name    : NarrowDNF.ConditionalExpectation.squaredError_decomposition
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:19:33.41233+00:00
-- url     : https://prove2.me/theorems/1cc80b6d-3868-4d6e-8c22-15a3faf04463
-- title:
--   The weighted Pythagorean identity for finite conditional expectation
-- statement:
--   Let \(A,B\) be finite, \(\phi:A\to B\), and let \(w(a)>0\) for every \(a\in A\). For \(F:A\to\mathbb R\), let \(M(a)\) be the \(w\)-weighted mean of \(F\) on the fiber containing \(a\). Define \(\|H\|_w^2=\sum_a w(a)H(a)^2\). For every readout \(G:B\to\mathbb R\),
--   $$\|F-G\circ\phi\|_w^2=\|F-M\|_w^2+\|M-G\circ\phi\|_w^2.$$
--   No normalization of the positive weights is required. This decomposition exhibits conditional expectation as the least-squares projection onto functions that are constant on each partition atom.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L118-L135

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
import Theorems.Thm_NarrowDNF_ConditionalExpectation_residual_orthogonal

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem NarrowDNF.ConditionalExpectation.squaredError_decomposition (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (fun a => G (φ a)) =
      squaredError w F (conditional φ w F) +
        squaredError w (conditional φ w F) (fun a => G (φ a)) := by sorry
