-- Prove2me | Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_eq_productKernel
-- name    : NarrowDNF.BourgainNoise.tensorNoise_eq_productKernel
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:09:03.200497+00:00
-- url     : https://prove2.me/theorems/eee9c176-3e6f-4b7f-8c98-4d76fa8cc7f1
-- title:
--   Product-kernel representation of spectral tensor noise
-- statement:
--   Let \(\iota\) be finite, \(p\in\mathbb R\), \(\rho:\iota\to\mathbb R\), and \(f:\{0,1\}^{\iota}\to\mathbb R\). Put \(b_p(1)=p\), \(b_p(0)=1-p\), \(z_p(b)=(b-p)/\sqrt{p(1-p)}\), \(\chi_S(x)=\prod_{i\in S}z_p(x_i)\), and \(\widehat f(S)=\sum_y\prod_i b_p(y_i)f(y)\chi_S(y)\). Define \(T_\rho f(x)=\sum_S(\prod_{i\in S}\rho_i)\widehat f(S)\chi_S(x)\). For every input \(x\),
--   $$T_\rho f(x)=\sum_y\prod_i\bigl[b_p(y_i)(1+\rho_i z_p(x_i)z_p(y_i))\bigr]f(y).$$
--   The identity is algebraic for arbitrary real parameters, with square root defined as zero on negative arguments and division by zero defined as zero; for \(0<p<1\) these are the usual biased Fourier quantities.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L202-L239

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

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

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

theorem NarrowDNF.BourgainNoise.tensorNoise_eq_productKernel (p : ℝ) (ρ : ι → ℝ)
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    tensorNoise p ρ f x = ∑ y : ι → Bool,
      (∏ i, ProductMeasure.bitWeight p (y i) *
        (1 + ρ i * Fourier.standardBit p (x i) * Fourier.standardBit p (y i))) * f y := by sorry
