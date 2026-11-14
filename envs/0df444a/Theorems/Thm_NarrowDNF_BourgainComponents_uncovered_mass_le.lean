-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_uncovered_mass_le
-- name    : NarrowDNF.BourgainComponents.uncovered_mass_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:27.451604+00:00
-- url     : https://prove2.me/theorems/9391e994-7bfe-4469-9500-71b101668bf4
-- title:
--   Charging uncovered component mass to outside coordinates
-- statement:
--   Let \(\iota\) be finite, let \(F\) be a finite family of subsets of \(\iota\), let \(c_S\in\mathbb R\) be values assigned to finite subsets, and let \(A\subseteq\iota\). Define the coordinate square sums \(Q_i=\sum_{S\in F:i\in S}c_S^2\). Then
--   $$\sum_{\substack{S\in F\\S\nsubseteq A}}c_S^2\le\sum_{i\notin A}Q_i.$$
--   Every component not completely supported inside \(A\) is therefore controlled by square mass incident to coordinates outside \(A\). There is no degree cutoff or threshold hypothesis in this estimate.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L92-L119

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
import Definitions.Def_NarrowDNF_BourgainComponents
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

theorem NarrowDNF.BourgainComponents.uncovered_mass_le (F : Finset (Finset ι)) (c : Finset ι → ℝ) (A : Finset ι) :
    (∑ S ∈ F, if S ⊆ A then 0 else c S ^ 2) ≤
      ∑ i, if i ∈ A then 0 else coordinateSquare F c i := by sorry
