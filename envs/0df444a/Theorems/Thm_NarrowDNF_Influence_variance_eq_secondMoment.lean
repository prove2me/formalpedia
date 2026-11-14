-- Prove2me | Theorems.Thm_NarrowDNF_Influence_variance_eq_secondMoment
-- name    : NarrowDNF.Influence.variance_eq_secondMoment
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:58.488785+00:00
-- url     : https://prove2.me/theorems/2747f498-c9c4-46f2-a3da-80190c0a5077
-- title:
--   Variance equals the second moment minus the square of the mean
-- statement:
--   For a finite Boolean cube, let $w_p(x)=\prod_i[p\,\mathbf1_{x_i=1}+(1-p)\mathbf1_{x_i=0}]$ and $\mathbb E_pF=\sum_xw_p(x)F(x)$. Define $\operatorname{Var}_p(F)=\mathbb E_p[(F-\mathbb E_pF)^2]$. For every real parameter $p$ and real function $F$,
--   $$
--   \operatorname{Var}_p(F)=\mathbb E_p[F^2]-(\mathbb E_pF)^2.
--   $$
--   For $0\le p\le1$ this is the usual probability identity. The finite algebraic formulation also holds outside that interval, where the weights can be signed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L80-L94

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Influence
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.Influence.variance_eq_secondMoment (p : ℝ) (F : (ι → Bool) → ℝ) :
    variance p F = ProductMeasure.expectation p (fun x => F x ^ 2) -
      ProductMeasure.expectation p F ^ 2 := by sorry
