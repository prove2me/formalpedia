-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_tensor
-- name    : NarrowDNF.Hypercontractivity.contract24_tensor
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:25:45.180427+00:00
-- url     : https://prove2.me/theorems/74672b9f-5275-4639-a36c-05716fdca3d7
-- title:
--   Two-factor tensorization of fourth-moment contractions
-- statement:
--   Let $A,B$ be finite sets with nonnegative weights $w,v$. Suppose maps $T$ on real functions on $A$ and $U$ on real functions on $B$ each satisfy the weighted L2-to-L4 moment inequality. No linearity is required. For $F:A\times B\to\mathbb R$, define $VF(a,b)=T[a'\mapsto U(F(a',\cdot))(b)](a)$. Then
--   $$
--   \sum_{a,b}w(a)v(b)VF(a,b)^4
--   \le\left(\sum_{a,b}w(a)v(b)F(a,b)^2\right)^2.
--   $$
--   Here the scalar assumption for $T$, for example, is $\sum_a w(a)(Th(a))^4\le(\sum_a w(a)h(a)^2)^2$ for every $h$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L93-L128

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
import Theorems.Thm_NarrowDNF_Hypercontractivity_vector_moment_le

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

theorem NarrowDNF.Hypercontractivity.contract24_tensor {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {v : β → ℝ} (hv : ∀ y, 0 ≤ v y)
    {T : (α → ℝ) → α → ℝ} {U : (β → ℝ) → β → ℝ}
    (hT : Contract24 w T) (hU : Contract24 v U) :
    Contract24 (fun z : α × β => w z.1 * v z.2)
      (fun f z => T (fun a => U (fun b => f (a,b)) z.2) z.1) := by sorry
