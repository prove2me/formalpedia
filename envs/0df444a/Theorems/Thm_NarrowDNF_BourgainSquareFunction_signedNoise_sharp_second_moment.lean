-- Prove2me | Theorems.Thm_NarrowDNF_BourgainSquareFunction_signedNoise_sharp_second_moment
-- name    : NarrowDNF.BourgainSquareFunction.signedNoise_sharp_second_moment
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:16.063201+00:00
-- url     : https://prove2.me/theorems/2f3f78af-f054-44e0-8d3e-b050df5416aa
-- title:
--   The exact second moment after sharp noise in the sign coordinates
-- statement:
--   Let \(I\) be finite, \(p\in\mathbb R\), \(f:\{0,1\}^I\to\mathbb R\), and \(x\in\{0,1\}^I\). Put \(\chi_S^p(u)=\prod_{i\in S}\frac{u_i-p}{\sqrt{p(1-p)}}\), \(\widehat f_p(S)=\mathbb E_p[f\chi_S^p]\), and \(a_S(x)=\widehat f_p(S)\chi_S^p(x)\). Here \(\mathbb E_p\) is the product weighted sum; square roots of negative numbers and division by zero have value zero. Define the signed-noise function on an independent uniform cube by
--   $$G_x(y)=\sum_{S\subseteq I}3^{-|S|}a_S(x)\chi_S^{1/2}(y).$$
--   If \(T_\rho\) multiplies its uniform Fourier coefficient at \(S\) by \(\rho^{|S|}\), then for \(\rho=\sqrt{1/3}\),
--   $$\mathbb E_{y\sim\mu_{1/2}}[(T_\rho G_x)(y)^2]=\sum_{S\subseteq I}\frac{a_S(x)^2}{3^{3|S|}}.$$
--   Only the auxiliary sign cube is interpreted probabilistically; no restriction on \(p\) is assumed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L145-L169

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
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval

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

theorem NarrowDNF.BourgainSquareFunction.signedNoise_sharp_second_moment (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ProductMeasure.expectation (1/2) (fun y =>
      BourgainNoise.tensorNoise (1/2) (fun _ => Hypercontractivity.sharpRho)
        (fun z => signedNoise p f z x) y ^ 2) =
      ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
        (3 : ℝ)^(3 * Fourier.degree s) := by sorry
