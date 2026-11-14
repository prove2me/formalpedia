-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_vector_moment_le
-- name    : NarrowDNF.Hypercontractivity.vector_moment_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:43.148938+00:00
-- url     : https://prove2.me/theorems/d2b0892e-928d-4f63-a6aa-75dc4b0798be
-- title:
--   A weighted family of squared contraction outputs satisfies a mixed-norm bound
-- statement:
--   Let $A,B$ be finite, let $w:A\to[0,\infty)$ and $v:B\to[0,\infty)$, and suppose $T$ satisfies $\sum_xw(x)(Th(x))^4\le(\sum_xw(x)h(x)^2)^2$ for every real $h$. For any family $(f_y)_{y\in B}$ of real functions on $A$,
--   $$
--   \sum_xw(x)\left(\sum_yv(y)(Tf_y(x))^2\right)^2
--   \le\left(\sum_yv(y)\sum_xw(x)f_y(x)^2\right)^2.
--   $$
--   Neither weight family is required to be normalized. This is the mixed-norm estimate needed in the two-factor contraction theorem.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L53-L91

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
import Theorems.Thm_NarrowDNF_Hypercontractivity_cross_moment_le

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

theorem NarrowDNF.Hypercontractivity.vector_moment_le {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {T : (α → ℝ) → α → ℝ} (hT : Contract24 w T)
    (v : β → ℝ) (hv : ∀ y, 0 ≤ v y) (f : β → α → ℝ) :
    (∑ x, w x * (∑ y, v y * (T (f y) x)^2)^2) ≤
      (∑ y, v y * (∑ x, w x * (f y x)^2))^2 := by sorry
