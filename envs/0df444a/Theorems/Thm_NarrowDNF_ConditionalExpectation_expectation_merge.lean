-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_merge
-- name    : NarrowDNF.ConditionalExpectation.expectation_merge
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:24.893755+00:00
-- url     : https://prove2.me/theorems/612a586c-d53d-492b-816d-b743417ade67
-- title:
--   Finite Fubini across a coordinate partition
-- statement:
--   Let \(I\) be finite, \(P\subseteq I\), \(p\in\mathbb R\), and \(F:\{0,1\}^I\to\mathbb R\). For any coordinate set \(A\), write \(\mathbb E_p^A\) for the finite sum weighted by \(\prod_{i\in A}p^{x_i}(1-p)^{1-x_i}\). If \(z\) and \(y\) are assignments on \(P\) and \(I\setminus P\), let \(z\sqcup y\) be their merged assignment. Then
--   $$\mathbb E_p^I F=\mathbb E_{p,z}^P\,\mathbb E_{p,y}^{I\setminus P}[F(z\sqcup y)].$$
--   This is the finite product decomposition of expectation. As an identity of weighted sums, it holds for every real \(p\), including outside the probability range.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalIndependence.lean#L13-L30

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
import Definitions.Def_NarrowDNF_Adaptive
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
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.ConditionalExpectation.expectation_merge (p : ℝ) (P : ι → Prop) [DecidablePred P] (F : Cube ι → ℝ) :
    expectation p F = expectation p (fun z => expectation p (fun y => F (merge P z y))) := by sorry
