-- Prove2me | Theorems.Thm_NarrowDNF_HatamiActivation_threshold_load_le
-- name    : NarrowDNF.HatamiActivation.threshold_load_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:02.240323+00:00
-- url     : https://prove2.me/theorems/53c70d15-1c8d-4df2-b192-541d34010e6c
-- title:
--   Multiplicity load of a threshold activation family
-- statement:
--   Let $I$ be a finite coordinate set, $p\in\mathbb R$, $k\ge0$, and $\delta>0$. Let $\mathcal A$ be a family of subsets of $I$ with $|S|\le k$, carrying nonnegative masses $m_S$. Put $b_T=\sum_{S\in\mathcal A,\,T\subseteq S}m_S$ and $w_{p,T}(x)=\prod_{i\in T}p^{x_i}(1-p)^{1-x_i}$. The threshold family $J$ fires $T$ when $|T|\le k$ and $\delta w_{p,T}(x)\le b_T$. Its multiplicity load, defined using product-weight event sums, satisfies
--   $$\operatorname{load}_p(J)=\sum_T|T|\,P_p(J_T)\le\frac{k2^{2k}}{\delta}\sum_{S\in\mathcal A}m_S.$$
--   This controls the total number of revealed coordinates counted with activation multiplicity.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L173-L209

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
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiActivation_threshold_probability_le

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

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiActivation
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiActivation.threshold_load_le {k p δ : ℝ} (hk0 : 0 ≤ k) (hδ : 0 < δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S)
    (hcard : ∀ S ∈ retained, (S.card : ℝ) ≤ k) :
    (thresholdActivation k p δ retained m).load p ≤
      (k * (2 : ℝ)^(2*k) / δ) * ∑ S ∈ retained, m S := by sorry
