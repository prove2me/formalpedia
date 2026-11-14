-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_pointwise_bourgain_split
-- name    : NarrowDNF.BourgainComponents.pointwise_bourgain_split
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:37.605206+00:00
-- url     : https://prove2.me/theorems/4d9d3eb8-fc3e-4f07-8e8e-12ac430d4306
-- title:
--   Pointwise three-part Bourgain decomposition
-- statement:
--   Let \(\iota\) be finite, \(F\) a finite family of subsets of \(\iota\), and \(c_S\in\mathbb R\). For \(k,M\in\mathbb N\), assume \(|S|\le k\) for all \(S\in F\); let \(\eta,\tau\in\mathbb R\). Define \(T=\sum_{S\in F}c_S^2\mathbf1_{|c_S|\le\eta}\), \(Q_i=\sum_{S\in F:i\in S}c_S^2\), and \(A=\{i:Q_i>\tau^2\}\). Then
--   $$T\le M^k\eta^2+\sum_iQ_i\mathbf1_{Q_i\le\tau^2}+\mathbf1_{|A|\ge M}\sum_{S\in F}c_S^2.$$
--   The three terms isolate mass on a small collection of large coordinates, contributions involving small coordinates, and the exceptional case of many large coordinates.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L169-L209

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
import Theorems.Thm_NarrowDNF_BourgainComponents_truncated_mass_split

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

theorem NarrowDNF.BourgainComponents.pointwise_bourgain_split (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η τ : ℝ) :
    truncatedMass F c η ≤ (M : ℝ)^k * η^2 +
      (∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0) +
      (if M ≤ (largeCoordinates F c τ).card then ∑ S ∈ F, c S^2 else 0) := by sorry
