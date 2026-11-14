-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_uniform_spectral_contract24
-- name    : NarrowDNF.Hypercontractivity.uniform_spectral_contract24
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:34:47.018323+00:00
-- url     : https://prove2.me/theorems/cb63e511-3665-4f68-b353-d3c75484edde
-- title:
--   Sharp L2-to-L4 hypercontractivity for uniform-cube spectral noise
-- statement:
--   Let $I$ be any finite coordinate set, $f:\{0,1\}^I\to\mathbb R$, and $\rho\in\mathbb R$ satisfy $3\rho^2\le1$. Write $\mathbb E$ for uniform expectation and let $T_\rho$ be Fourier noise: each Walsh coefficient indexed by $S$ is multiplied by $\rho^{|S|}$. Then
--   $$
--   \mathbb E[(T_\rho f)^4]\le\bigl(\mathbb E[f^2]\bigr)^2.
--   $$
--   The condition allows negative $\rho$, includes the sharp endpoints $\rho=\pm1/\sqrt3$, and is independent of dimension. The assertion concerns the actual Fourier-defined noise operator.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L306-L324

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_eq_productKernel
import Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_product

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
open NarrowDNF.Hypercontractivity
attribute [local instance] Classical.decEq
variable {α β : Type*} [Fintype α] [Fintype β]

theorem NarrowDNF.Hypercontractivity.uniform_spectral_contract24 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => ρ) f x ^ 4) ≤
        (ProductMeasure.expectation (1/2) (fun x => f x ^ 2))^2 := by sorry
