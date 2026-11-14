-- Prove2me | Theorems.Thm_NarrowDNF_BourgainComponents_truncated_mass_split
-- name    : NarrowDNF.BourgainComponents.truncated_mass_split
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:25:54.028464+00:00
-- url     : https://prove2.me/theorems/e5a19e25-055c-471f-b9b6-d4ae5ff25d2f
-- title:
--   Splitting truncated mass by covered and uncovered coordinates
-- statement:
--   Let \(\iota\) be finite, let \(F\) be a finite family of coordinate subsets, and assign a real value \(c_S\) to every finite subset \(S\). Let \(A\subseteq\iota\), \(k\in\mathbb N\), and \(\eta\in\mathbb R\), with \(|S|\le k\) for every \(S\in F\). Write \(Q_i=\sum_{S\in F:i\in S}c_S^2\). Then
--   $$\sum_{S\in F}c_S^2\mathbf1_{|c_S|\le\eta}\le(|A|+1)^k\eta^2+\sum_{i\notin A}Q_i.$$
--   The estimate separates components supported within a selected coordinate set from those extending outside it, preparing the pointwise Bourgain decomposition.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L150-L167

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
import Theorems.Thm_NarrowDNF_BourgainComponents_contained_truncated_mass_le
import Theorems.Thm_NarrowDNF_BourgainComponents_uncovered_mass_le

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

theorem NarrowDNF.BourgainComponents.truncated_mass_split (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (A : Finset ι) (k : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η : ℝ) :
    truncatedMass F c η ≤ ((A.card+1 : ℕ) : ℝ)^k * η^2 +
      ∑ i, if i ∈ A then 0 else coordinateSquare F c i := by sorry
