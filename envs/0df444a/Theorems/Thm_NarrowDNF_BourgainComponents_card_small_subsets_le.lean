-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_card_small_subsets_le
-- name    : NarrowDNF.BourgainComponents.card_small_subsets_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:16:22.104845+00:00
-- url     : https://prove2.me/theorems/16389925-a1bb-48eb-8de5-396cf7f476af
-- title:
--   Polynomial bound for the number of small subsets
-- statement:
--   Let \(A\) be a finite subset of a coordinate set \(\iota\), and let \(k\in\mathbb N\). The number of subsets of \(A\) containing at most \(k\) elements satisfies
--   $$\bigl|\{S\subseteq A:|S|\le k\}\bigr|\le(|A|+1)^k.$$
--   The bound includes the empty subset and holds when \(A\) is empty or \(k=0\). It provides a simple polynomial estimate, in the size of the available coordinate set, for the number of possible component supports of bounded degree.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L54-L74

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
import Theorems.Thm_NarrowDNF_BourgainComponents_sum_powers_le

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
omit [Fintype ι]

theorem NarrowDNF.BourgainComponents.card_small_subsets_le (A : Finset ι) (k : ℕ) :
    (A.powerset.filter fun S => S.card ≤ k).card ≤ (A.card+1)^k := by sorry
