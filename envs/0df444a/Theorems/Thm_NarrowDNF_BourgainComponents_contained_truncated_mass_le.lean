-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_contained_truncated_mass_le
-- name    : NarrowDNF.BourgainComponents.contained_truncated_mass_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:45.565329+00:00
-- url     : https://prove2.me/theorems/a797855e-20bb-478c-9f8d-1cc91c53c574
-- title:
--   Truncated component mass on a fixed support set
-- statement:
--   Let \(F\) be a finite family of finite subsets of a coordinate set \(\iota\), let \(c\) assign a real number \(c_S\) to each finite subset, and let \(A\subseteq\iota\) be finite. Suppose \(k\in\mathbb N\) and \(|S|\le k\) for every \(S\in F\). For any real threshold \(\eta\),
--   $$\sum_{\substack{S\in F\\S\subseteq A}}c_S^2\mathbf1_{|c_S|\le\eta}\le(|A|+1)^k\eta^2.$$
--   Thus components supported entirely within \(A\) have a cardinality-controlled contribution to truncated squared mass. No probabilistic assumptions on the numbers \(c_S\) are needed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L128-L148

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
import Theorems.Thm_NarrowDNF_BourgainComponents_card_small_subsets_le

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

theorem NarrowDNF.BourgainComponents.contained_truncated_mass_le (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (A : Finset ι) (k : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η : ℝ) :
    (∑ S ∈ F, if S ⊆ A then (if |c S| ≤ η then c S ^ 2 else 0) else 0) ≤
      ((A.card+1 : ℕ) : ℝ)^k * η^2 := by sorry
