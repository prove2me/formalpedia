-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_product
-- name    : NarrowDNF.Hypercontractivity.contract24_product
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:28.203737+00:00
-- url     : https://prove2.me/theorems/6e8c028e-db6f-4d26-90d1-3e68e6283234
-- title:
--   Finite products preserve a two-point L2-to-L4 kernel contraction
-- statement:
--   Let $w:\{0,1\}\to[0,\infty)$, let $K$ be any real two-point kernel, and put $(Af)(b)=\sum_c w(c)K(b,c)f(c)$. Assume $\sum_b w(b)(Af(b))^4\le(\sum_b w(b)f(b)^2)^2$ for every real $f$. For any finite coordinate set $I$, set $W(x)=\prod_{i\in I}w(x_i)$ and $(P_KF)(x)=\sum_y\prod_i[w(y_i)K(x_i,y_i)]F(y)$. Then
--   $$
--   \sum_xW(x)(P_KF(x))^4\le\left(\sum_xW(x)F(x)^2\right)^2.
--   $$
--   Neither normalization of $w$ nor positivity of $K$ is assumed. The bound has no dimension factor.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L239-L272

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
import Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_tensor
import Theorems.Thm_NarrowDNF_Hypercontractivity_productOperator_option

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

theorem NarrowDNF.Hypercontractivity.contract24_product (w : Bool → ℝ) (hw : ∀ b, 0 ≤ w b)
    (K : Bool → Bool → ℝ) (hK : Contract24 w (kernelOperator w K))
    (ι : Type*) [Fintype ι] :
    Contract24 (productWeight (ι := ι) w) (productOperator w K) := by sorry
