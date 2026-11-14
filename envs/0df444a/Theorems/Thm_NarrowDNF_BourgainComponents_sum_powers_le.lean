-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_sum_powers_le
-- name    : NarrowDNF.BourgainComponents.sum_powers_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:33.730193+00:00
-- url     : https://prove2.me/theorems/4cd27197-89b5-4b6b-9363-60be2491e37e
-- title:
--   A polynomial bound for a finite geometric sum
-- statement:
--   For arbitrary nonnegative integers \(n\) and \(k\), the finite geometric sum obeys
--   $$\sum_{j=0}^{k}n^j\le(n+1)^k.$$
--   Powers have their usual natural-number meaning, including \(n^0=1\). Consequently the result covers \(n=0\) and \(k=0\). This estimate supplies the elementary numerical step in bounding the number of subsets of size at most \(k\) by a single explicit polynomial bound in the size of the underlying set.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L39-L52

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents

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
open NarrowDNF.BourgainComponents
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainComponents.sum_powers_le (n k : ℕ) : (∑ j ∈ Finset.range (k+1), n^j) ≤ (n+1)^k := by sorry
