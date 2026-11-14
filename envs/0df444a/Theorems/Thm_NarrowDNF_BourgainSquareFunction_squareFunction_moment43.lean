-- Prove2me | Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_moment43
-- name    : NarrowDNF.BourgainSquareFunction.squareFunction_moment43
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:47:07.787599+00:00
-- url     : https://prove2.me/theorems/bf3378bd-e2e5-4a03-96fb-d89fde054e17
-- title:
--   A dimension-free four-thirds-moment estimate for the Fourier square function
-- statement:
--   Let \(I\) be finite, \(0<p<1\), \(f:\{0,1\}^I\to\mathbb R\), and \(k\) a nonnegative integer. With biased orthonormal Fourier coefficients and characters, set
--   $$Q_{p,k}f(x)=\sum_{|S|\le k}(\widehat f_p(S)\chi_S^p(x))^2.$$
--   Then the Bernoulli product expectations satisfy
--   $$\mathbb E_p[(Q_{p,k}f)^{2/3}]\le3^{2k}\mathbb E_p[|f|^{4/3}].$$
--   The left side is the \(4/3\)-moment of the square root of this sum of squares. The constant depends only on the degree cutoff, giving the moment estimate required in the small-component argument.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L259-L280

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainDuality
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_BourgainSquareFunction
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainDuality_dual_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_negative_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_positive_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_selfAdjoint
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_rpow_le_sign_moment43
import Theorems.Thm_NarrowDNF_Fourier_expansion
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF.BourgainNoise
end NarrowDNF.BourgainNoise

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainSquareFunction.squareFunction_moment43 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    ProductMeasure.expectation p (fun x => squareFunction p f k x ^ (2/3 : ℝ)) ≤
      (3 : ℝ)^(2*k) * BourgainDuality.moment43 (ProductMeasure.weight p) f := by sorry
