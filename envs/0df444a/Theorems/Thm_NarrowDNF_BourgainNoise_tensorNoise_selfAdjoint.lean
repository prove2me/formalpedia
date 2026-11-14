-- Prove2me | Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_selfAdjoint
-- name    : NarrowDNF.BourgainNoise.tensorNoise_selfAdjoint
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:09:53.345366+00:00
-- url     : https://prove2.me/theorems/18c9204b-db44-420a-b9b8-c673d65a2b74
-- title:
--   Self-adjointness of spectral tensor noise
-- statement:
--   Let \(\iota\) be finite, \(p\in\mathbb R\), and \(\rho:\iota\to\mathbb R\). Use product weights \(\mu_p(x)=\prod_i b_p(x_i)\), where \(b_p(1)=p\) and \(b_p(0)=1-p\). Define \(\chi_S(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\), \(\widehat f(S)=\sum_x\mu_p(x)f(x)\chi_S(x)\), and \(T_\rho f(x)=\sum_S(\prod_{i\in S}\rho_i)\widehat f(S)\chi_S(x)\). For all real functions \(f,g\),
--   $$\sum_x\mu_p(x)(T_\rho f)(x)g(x)=\sum_x\mu_p(x)f(x)(T_\rho g)(x).$$
--   This self-adjointness identity holds algebraically for all real parameters, with square root defined as zero on negative arguments and division by zero defined as zero; in the probability range it concerns the biased weighted pairing.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L241-L273

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainNoise
end NarrowDNF.BourgainNoise

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainNoise
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainNoise.tensorNoise_selfAdjoint (p : ℝ) (ρ : ι → ℝ)
    (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => tensorNoise p ρ f x * g x) =
      ProductMeasure.expectation p (fun x => f x * tensorNoise p ρ g x) := by sorry
