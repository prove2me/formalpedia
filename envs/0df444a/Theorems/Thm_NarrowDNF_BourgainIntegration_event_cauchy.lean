-- Prove2me | Theorems.Thm_NarrowDNF_BourgainIntegration_event_cauchy
-- name    : NarrowDNF.BourgainIntegration.event_cauchy
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:04:13.298559+00:00
-- url     : https://prove2.me/theorems/193ce6a9-60b7-4735-8762-3973ffb11438
-- title:
--   Weighted Cauchy–Schwarz on an event
-- statement:
--   Let \(\alpha\) be finite, let \(w_x\ge0\) be weights, let \(F_x\ge0\) be a real observable, and let \(B\subseteq\alpha\) be an event. Then
--   $$\sum_{x\in B}w_xF_x\le\sqrt{\sum_xw_xF_x^2}\sqrt{\sum_{x\in B}w_x}.$$
--   The weights need not be a probability distribution. For normalized weights this bounds the expectation restricted to an event by the second-moment norm of the observable times the square root of the event probability. This is the estimate used to control the exceptional part of the integrated Bourgain decomposition.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainIntegration.lean#L36-L55

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
variable {α : Type*} [Fintype α]

theorem NarrowDNF.BourgainIntegration.event_cauchy (w F : α → ℝ) (hw : ∀ x, 0 ≤ w x) (_hF : ∀ x, 0 ≤ F x)
    (B : α → Prop) [DecidablePred B] :
    (∑ x, w x * (if B x then F x else 0)) ≤
      Real.sqrt (∑ x, w x * F x^2) * Real.sqrt (∑ x, w x * (if B x then 1 else 0)) := by sorry
