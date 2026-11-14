-- Prove2me | Theorems.Thm_NarrowDNF_BourgainIntegration_large_event_probability_le
-- name    : NarrowDNF.BourgainIntegration.large_event_probability_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:04:22.412244+00:00
-- url     : https://prove2.me/theorems/ff549928-7ad9-4a52-a59e-3699b1e9b9bf
-- title:
--   Probability bound for many large coordinate squares
-- statement:
--   Let \(\alpha\) and \(\iota\) be finite, let \(w:\alpha\to\mathbb R\) have nonnegative values, and let \(F\) be a finite family of subsets of \(\iota\). Assign real values \(c_S(x)\) for \(x\in\alpha\) and finite supports \(S\). Define \(Q_i(x)=\sum_{S\in F:i\in S}c_S(x)^2\) and \(A(x)=\{i:Q_i(x)>\tau^2\}\). For every positive integer \(M\) and real \(\tau>0\),
--   $$\sum_xw_x\mathbf1_{|A(x)|\ge M}\le\frac{\sum_xw_x\sum_iQ_i(x)}{M\tau^2}.$$
--   Normalized weights interpret this as a probability estimate for having many large coordinate squares; arbitrary nonnegative weights also satisfy it.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainIntegration.lean#L59-L77

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
import Definitions.Def_NarrowDNF_BourgainComponents
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
variable {α : Type*} [Fintype α]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainIntegration.large_event_probability_le (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : Finset (Finset ι)) (c : α → Finset ι → ℝ) (M : ℕ) (hM : 0 < M)
    (τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * (if M ≤ (largeCoordinates F (c x) τ).card then 1 else 0)) ≤
      (∑ x, w x * ∑ i, coordinateSquare F (c x) i) / ((M : ℝ)*τ^2) := by sorry
