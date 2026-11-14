-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_intersection_kernel_sum_le
-- name    : NarrowDNF.HatamiCrossTerms.intersection_kernel_sum_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:37.871973+00:00
-- url     : https://prove2.me/theorems/45003c32-f16e-4f39-8072-61bb32a86d84
-- title:
--   Thresholded summation over all pair intersections
-- statement:
--   Let $I$ be finite, $0<p<1$, $\delta\ge0$, and let $\mathcal A$ satisfy $|S|\le k$. Suppose $0\le a_S\le m_S$ on $\mathcal A$. Let $J$ be the threshold activation with masses $m$, cutoff $k$, and parameter $\delta$; let $K_J(T)=E_p[\mathbf1_{\neg J_T}/w_{p,T}^2]$. Then
--   $$\sum_{S,R\in\mathcal A}a_Sa_RK_J(S\cap R)\le\delta\sum_{S\in\mathcal A}3^{|S|}a_S.$$
--   The estimate charges all ordered support pairs to individual retained supports, with no dependence on the ambient dimension.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L196-L231

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
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_bMass_mul_inactiveKernel_le
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_intersection_sum_le

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

theorem NarrowDNF.HatamiCrossTerms.intersection_kernel_sum_le {p k δ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (A : Finset (Finset ι)) (a m : Finset ι → ℝ)
    (ha : ∀ S ∈ A, 0 ≤ a S) (ham : ∀ S ∈ A, a S ≤ m S)
    (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k) :
    (∑ S ∈ A, ∑ R ∈ A, a S * a R *
      inactiveKernel p (thresholdActivation k p δ A m) (S ∩ R)) ≤
      δ * ∑ S ∈ A, (3:ℝ)^S.card * a S := by sorry
