-- Prove2me | Theorems.Thm_NarrowDNF_Hypercontractivity_cross_moment_le
-- name    : NarrowDNF.Hypercontractivity.cross_moment_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:58.523867+00:00
-- url     : https://prove2.me/theorems/6ff8013e-2809-4790-be89-caf2af64b5ca
-- title:
--   A fourth-moment contraction controls mixed squared outputs
-- statement:
--   Let $A$ be finite with nonnegative weights $w$, and suppose a map $T$ satisfies $\sum_xw(x)(Th(x))^4\le(\sum_xw(x)h(x)^2)^2$ for every real function $h$. For arbitrary real functions $f,g$,
--   $$
--   \sum_xw(x)(Tf(x))^2(Tg(x))^2
--   \le\left(\sum_xw(x)f(x)^2\right)\left(\sum_xw(x)g(x)^2\right).
--   $$
--   The weights need not sum to one, and the map need not be linear. This mixed estimate is the scalar input for the vector-valued tensorization argument.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/UniformHypercontractivity.lean#L27-L51

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
import Definitions.Def_NarrowDNF_UniformHypercontractivity

namespace NarrowDNF.Hypercontractivity
end NarrowDNF.Hypercontractivity
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Hypercontractivity
attribute [local instance] Classical.decEq
variable {α β : Type*} [Fintype α] [Fintype β]

theorem NarrowDNF.Hypercontractivity.cross_moment_le {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {T : (α → ℝ) → α → ℝ} (hT : Contract24 w T) (f g : α → ℝ) :
    (∑ x, w x * (T f x)^2 * (T g x)^2) ≤
      (∑ x, w x * (f x)^2) * (∑ x, w x * (g x)^2) := by sorry
