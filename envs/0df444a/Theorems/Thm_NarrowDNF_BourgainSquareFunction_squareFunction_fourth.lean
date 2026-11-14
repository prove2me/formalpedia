-- Prove2me | Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_fourth
-- name    : NarrowDNF.BourgainSquareFunction.squareFunction_fourth
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:22.252003+00:00
-- url     : https://prove2.me/theorems/600a33d4-af7f-43e8-af14-65a242f76577
-- title:
--   A dimension-free fourth-moment estimate for the low-degree square function
-- statement:
--   Let \(I\) be finite, \(0<p<1\), \(f:\{0,1\}^I\to\mathbb R\), and \(k\ge0\) an integer. For Bernoulli product measure \(\mu_p\), let \(\widehat f_p(S)\) and \(\chi_S^p\) denote its orthonormal Fourier coefficients and characters. Define the squared low-degree square function by
--   $$Q_{p,k}f(x)=\sum_{|S|\le k}(\widehat f_p(S)\chi_S^p(x))^2.$$
--   Then
--   $$\mathbb E_p[(Q_{p,k}f)^2]\le3^{4k}\mathbb E_p[f^4].$$
--   Equivalently, the fourth moment of \(\sqrt{Q_{p,k}f}\) is bounded independently of both the dimension and the bias.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L198-L228

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
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_BourgainSquareFunction
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_negative_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_positive_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_low_degree_le_damped
import Theorems.Thm_NarrowDNF_Fourier_expansion
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
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

theorem NarrowDNF.BourgainSquareFunction.squareFunction_fourth {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    ProductMeasure.expectation p (fun x => squareFunction p f k x ^ 2) ≤
      (3 : ℝ)^(4*k) * ProductMeasure.expectation p (fun x => f x ^ 4) := by sorry
