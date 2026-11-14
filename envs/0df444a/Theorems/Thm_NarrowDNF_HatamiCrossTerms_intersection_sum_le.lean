-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_intersection_sum_le
-- name    : NarrowDNF.HatamiCrossTerms.intersection_sum_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:07.544415+00:00
-- url     : https://prove2.me/theorems/e22d432f-2630-42cd-8dd0-d162ac0b8aa9
-- title:
--   Enlarging exact intersections to all common subsets
-- statement:
--   Let $I$ be a finite set, $\mathcal A$ a finite family of subsets, and let $a_S\ge0$ for $S\in\mathcal A$. Let $K$ assign a nonnegative real number to every subset of $I$, and write $b_T=\sum_{S\in\mathcal A,\,T\subseteq S}a_S$. Then
--   $$\sum_{S,R\in\mathcal A}a_Sa_RK(S\cap R)\le\sum_{T\subseteq I}b_T^2K(T).$$
--   The right side replaces the exact intersection of a pair by every common subset. This combinatorial inequality is the summation step that makes the threshold kernel estimate applicable to all pairs at once.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L90-L133

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiCrossTerms.intersection_sum_le (A : Finset (Finset ι)) (a K : Finset ι → ℝ)
    (ha : ∀ S ∈ A, 0 ≤ a S) (hK : ∀ T, 0 ≤ K T) :
    (∑ S ∈ A, ∑ R ∈ A, a S * a R * K (S ∩ R)) ≤
      ∑ T : Finset ι, bMass A a T ^ 2 * K T := by sorry
