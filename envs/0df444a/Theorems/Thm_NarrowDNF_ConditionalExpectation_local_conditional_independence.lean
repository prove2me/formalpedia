-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_local_conditional_independence
-- name    : NarrowDNF.ConditionalExpectation.local_conditional_independence
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:44.857715+00:00
-- url     : https://prove2.me/theorems/5f934d4f-9dda-4324-8d26-827602ac885e
-- title:
--   Local functions factor after conditioning on their common coordinates
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(S,R\subseteq I\). Suppose real functions \(F,G\) on the Boolean cube depend only on coordinates in \(S\) and \(R\), respectively. Put \(H=S\cap R\), and let
--   $$M_HF(x)=\mathbb E_p[F(X)\mid X|_H=x|_H]$$
--   be the finite weighted conditional mean; define \(M_HG\) similarly. Then
--   $$\mathbb E_p[FG]=\mathbb E_p[(M_HF)(M_HG)].$$
--   This identifies the contribution of the shared coordinates to the product expectation. Strictly positive product weights ensure that every prescribed restriction has a well-defined positive conditioning mass.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalIndependence.lean#L53-L101

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
import Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_mul_of_complement_local
import Theorems.Thm_NarrowDNF_ConditionalExpectation_moment_restriction
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

theorem NarrowDNF.ConditionalExpectation.local_conditional_independence {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (S R : Finset ι) (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i ∈ S, x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i ∈ R, x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) =
      expectation p (fun x =>
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) F x *
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) G x) := by sorry
