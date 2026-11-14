-- Prove2me | Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_rpow_le_sign_moment43
-- name    : NarrowDNF.BourgainSquareFunction.squareFunction_rpow_le_sign_moment43
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:45:44.931011+00:00
-- url     : https://prove2.me/theorems/b53525c9-ef87-4ede-9a8f-f2f9eab2df73
-- title:
--   A pointwise sign-space bound for the low-degree Fourier square function
-- statement:
--   Let \(I\) be finite, \(p\in\mathbb R\), \(f:\{0,1\}^I\to\mathbb R\), \(k\ge0\) an integer, and \(x\) an input. Put \(\chi_S^p(u)=\prod_{i\in S}\frac{u_i-p}{\sqrt{p(1-p)}}\) and \(a_S(x)=\mathbb E_p[f\chi_S^p]\chi_S^p(x)\), where \(\mathbb E_p\) denotes the product weighted sum. Square roots of negative numbers and division by zero have value zero. Define
--   $$Q(x)=\sum_{|S|\le k}a_S(x)^2,\qquad G_x(y)=\sum_S3^{-|S|}a_S(x)\chi_S^{1/2}(y).$$
--   Then
--   $$Q(x)^{2/3}\le3^{2k}\mathbb E_{y\sim\mu_{1/2}}[|G_x(y)|^{4/3}].$$
--   This is a pointwise estimate in the original input; only the auxiliary sign variable is averaged. In particular, the formal statement imposes no bias-range hypothesis on \(p\).
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L230-L257

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
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_BourgainDuality_dual_contract24
import Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_selfAdjoint
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_low_degree_le_damped
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_signedNoise_sharp_second_moment
import Theorems.Thm_NarrowDNF_Hypercontractivity_uniform_spectral_contract24

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Hypercontractivity
end NarrowDNF.Hypercontractivity

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainSquareFunction.squareFunction_rpow_le_sign_moment43
    (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    squareFunction p f k x ^ (2/3 : ℝ) ≤ (3 : ℝ)^(2*k) *
      BourgainDuality.moment43 (ProductMeasure.weight (1/2)) (fun y => signedNoise p f y x) := by sorry
