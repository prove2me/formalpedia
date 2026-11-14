-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_eq_mean_of_variance_le_zero
-- name    : NarrowDNF.Fourier.eq_mean_of_variance_le_zero
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:12:20.470328+00:00
-- url     : https://prove2.me/theorems/9c503060-380e-425b-b379-11d45619d2ef
-- title:
--   Nonpositive variance forces pointwise constancy under a full-support product measure
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(f:\{0,1\}^I\to\mathbb R\). Put \(m=\mathbb E_p f\), and assume
--   $$\operatorname{Var}_p(f)=\mathbb E_p[(f-m)^2]\le0.$$
--   Then every input \(x\) satisfies
--   $$f(x)=m.$$
--   Thus zero variance gives literal pointwise constancy on the entire finite cube. The strict bias assumptions matter: they make every product weight positive, so no input can be excluded by a zero probability mass.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L426-L440

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Fourier
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.Fourier.eq_mean_of_variance_le_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (hf : Influence.variance p f ≤ 0) (x : ι → Bool) :
    f x = ProductMeasure.expectation p f := by sorry
