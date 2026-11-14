-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_moment_restriction
-- name    : NarrowDNF.ConditionalExpectation.moment_restriction
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:45.480274+00:00
-- url     : https://prove2.me/theorems/cda174fa-7413-4108-9713-a4839437b68a
-- title:
--   A fixed-coordinate first moment factors into marginal mass and free average
-- statement:
--   Let \(I\) be finite, \(P\subseteq I\), \(p\in\mathbb R\), \(F:\{0,1\}^I\to\mathbb R\), and \(z\in\{0,1\}^P\). Write \(w_{p,A}\) for the product weight on coordinates \(A\). The unnormalized first moment over the restriction fiber is
--   $$\sum_{x:\,x|_P=z}w_{p,I}(x)F(x)=w_{p,P}(z)\,\mathbb E_{p,y}^{I\setminus P}[F(z\sqcup y)].$$
--   Here \(z\sqcup y\) merges the fixed and free assignments. Thus the fiber moment is exactly its marginal assignment weight times an average over the complementary cube. The equality is algebraic and requires no restriction on the real parameter \(p\).
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L352-L370

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
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.ConditionalExpectation.moment_restriction (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : Cube ι → ℝ) (z : {i // P i} → Bool) :
    moment (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) F z =
      ProductMeasure.weight p z * ProductMeasure.expectation p (fun y => F (merge P z y)) := by sorry
