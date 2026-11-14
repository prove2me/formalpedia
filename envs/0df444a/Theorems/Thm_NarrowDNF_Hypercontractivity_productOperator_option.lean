-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_productOperator_option
-- name    : NarrowDNF.Hypercontractivity.productOperator_option
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:04.501209+00:00
-- url     : https://prove2.me/theorems/4019393b-4acf-4984-909e-3ccb15dfc2e6
-- title:
--   A product-kernel operator splits into one bit and the remaining coordinates
-- statement:
--   Let $I$ be finite, $w:\{0,1\}\to\mathbb R$, and $K:\{0,1\}^2\to\mathbb R$. For coordinates $I\cup\{*\}$, define $P_KF(x)=\sum_y\prod_j[w(y_j)K(x_j,y_j)]F(y)$, and define $Ah(b)=\sum_cw(c)K(b,c)h(c)$. If $x_I$ is the restriction of $x$ to $I$, then
--   $$
--   P_KF(x)=A\bigl[b\mapsto P_K(F(b,\cdot))(x_I)\bigr](x_*).
--   $$
--   In the inner operator the coordinate set is $I$. The identity holds for every real $F$, with no sign or normalization hypotheses on the weights or kernel.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L203-L237

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
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_UniformHypercontractivity

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

theorem NarrowDNF.Hypercontractivity.productOperator_option {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (K : Bool → Bool → ℝ) (f : (Option ι → Bool) → ℝ) (x : Option ι → Bool) :
    productOperator w K f x =
      kernelOperator w K (fun b => productOperator w K
        (fun y => f (Equiv.piOptionEquivProd.symm (b,y)))
        (fun i => x (some i))) (x none) := by sorry
