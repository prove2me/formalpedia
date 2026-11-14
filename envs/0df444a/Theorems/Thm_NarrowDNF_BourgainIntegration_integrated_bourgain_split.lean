-- Prove2me | Theorems.Thm_NarrowDNF_BourgainIntegration_integrated_bourgain_split
-- name    : NarrowDNF.BourgainIntegration.integrated_bourgain_split
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:34:37.195843+00:00
-- url     : https://prove2.me/theorems/9e0630a2-0f6b-4a9f-956d-c06a641d3065
-- title:
--   Integrated three-part Bourgain decomposition
-- statement:
--   Let \(\alpha,\iota\) be finite and \(w_x\ge0\) with \(\sum_xw_x=1\); write \(\mathbb E_w\) for weighted expectation. Let \(F\) be a finite family of subsets of \(\iota\), all of size at most \(k\in\mathbb N\), and let \(c_S(x)\in\mathbb R\). Fix a positive integer \(M\), real \(\eta\), and \(\tau>0\). Define \(T(x)=\sum_{S\in F}c_S(x)^2\mathbf1_{|c_S(x)|\le\eta}\), \(Q_i(x)=\sum_{S\in F:i\in S}c_S(x)^2\), and \(U(x)=\sum_{S\in F}c_S(x)^2\). Then
--   $$\mathbb E_wT\le M^k\eta^2+\tau^{2/3}\sum_i\mathbb E_wQ_i^{2/3}+\frac{\sqrt{\mathbb E_wU^2}\sqrt{\mathbb E_w\sum_iQ_i}}{\sqrt M\,\tau}.$$
--   This turns the pointwise decomposition into moment bounds.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainIntegration.lean#L80-L138

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
import Theorems.Thm_NarrowDNF_BourgainComponents_pointwise_bourgain_split
import Theorems.Thm_NarrowDNF_BourgainIntegration_event_cauchy
import Theorems.Thm_NarrowDNF_BourgainIntegration_large_event_probability_le
import Theorems.Thm_NarrowDNF_BourgainIntegration_small_square_le

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

theorem NarrowDNF.BourgainIntegration.integrated_bourgain_split (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (F : Finset (Finset ι)) (c : α → Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (hM : 0 < M)
    (η τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * truncatedMass F (c x) η) ≤
      (M:ℝ)^k * η^2 + τ^(2/3:ℝ) *
        (∑ i, ∑ x, w x * (coordinateSquare F (c x) i)^(2/3:ℝ)) +
      Real.sqrt (∑ x, w x * (∑ S ∈ F, c x S^2)^2) *
        Real.sqrt (∑ x, w x * ∑ i, coordinateSquare F (c x) i) /
          (Real.sqrt (M:ℝ) * τ) := by sorry
