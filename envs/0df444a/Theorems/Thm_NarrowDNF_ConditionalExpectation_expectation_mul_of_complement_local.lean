-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_mul_of_complement_local
-- name    : NarrowDNF.ConditionalExpectation.expectation_mul_of_complement_local
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:52.91165+00:00
-- url     : https://prove2.me/theorems/1f21c92c-07c4-4ece-91af-4b069639e890
-- title:
--   Complementary coordinate dependence factors weighted expectations
-- statement:
--   Let \(I\) be finite, \(P\subseteq I\), and \(p\in\mathbb R\). Suppose \(F,G:\{0,1\}^I\to\mathbb R\) satisfy: \(F(x)=F(y)\) whenever \(x,y\) agree on \(P\), and \(G(x)=G(y)\) whenever they agree on \(I\setminus P\). For the finite Bernoulli product weighted sum \(\mathbb E_p\),
--   $$\mathbb E_p[FG]=(\mathbb E_p F)(\mathbb E_p G).$$
--   For \(0\le p\le1\), this expresses independence of observables reading complementary coordinate sets. The formal identity itself allows arbitrary real \(p\), since it needs only algebraic factorization of product weights.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalIndependence.lean#L32-L51

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
import Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_merge
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict

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

theorem NarrowDNF.ConditionalExpectation.expectation_mul_of_complement_local (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i, ¬ P i → x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) = expectation p F * expectation p G := by sorry
