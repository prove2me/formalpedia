-- Prove2me | Theorems.Thm_NarrowDNF_BourgainIntegration_small_square_le
-- name    : NarrowDNF.BourgainIntegration.small_square_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:06:14.171674+00:00
-- url     : https://prove2.me/theorems/9d1aa7bb-d991-4cbf-a0e3-da369fdd0634
-- title:
--   Bounding a truncated square by its two-thirds moment
-- statement:
--   Let \(q\ge0\) and \(\tau>0\) be real numbers. The contribution of \(q\) below the cutoff \(\tau^2\) satisfies
--   $$q\mathbf1_{q\le\tau^2}\le\tau^{2/3}q^{2/3}.$$
--   The powers are ordinary nonnegative real powers, so the formula includes \(q=0\). Applied to coordinate square sums, this inequality converts a thresholded first-moment contribution into a fractional-moment quantity that can be controlled by square-function estimates. No probability space or normalization is part of the assertion.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainIntegration.lean#L13-L32

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents

namespace NarrowDNF.BourgainIntegration
end NarrowDNF.BourgainIntegration

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open NarrowDNF
open NarrowDNF.BourgainIntegration
open BourgainComponents
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem NarrowDNF.BourgainIntegration.small_square_le (q τ : ℝ) (hq : 0 ≤ q) (hτ : 0 < τ) :
    (if q ≤ τ^2 then q else 0) ≤ τ^(2/3:ℝ) * q^(2/3:ℝ) := by sorry
