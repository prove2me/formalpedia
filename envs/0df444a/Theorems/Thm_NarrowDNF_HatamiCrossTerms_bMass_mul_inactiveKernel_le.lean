-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_bMass_mul_inactiveKernel_le
-- name    : NarrowDNF.HatamiCrossTerms.bMass_mul_inactiveKernel_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:26.000209+00:00
-- url     : https://prove2.me/theorems/a9b7ed02-0a4b-4c84-93b2-93c63b9bf169
-- title:
--   A threshold bound for one inactive overlap kernel
-- statement:
--   Let $I$ be finite, $0<p<1$, $\delta\ge0$, and $\mathcal A$ a finite family with $|S|\le k$. Suppose real masses satisfy $a_S\le m_S$ for $S\in\mathcal A$. Put $b_T(a)=\sum_{S\in\mathcal A,\,T\subseteq S}a_S$, and let $J$ fire $T$ when $|T|\le k$ and $\delta w_{p,T}(x)\le b_T(m)$. Define $K_J(T)=E_p[\mathbf1_{\neg J_T}/w_{p,T}^2]$. Then, for every $T$,
--   $$b_T(a)K_J(T)\le2^{|T|}\delta.$$
--   No nonnegativity assumption on $a$ is required for this individual estimate.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L165-L194

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
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict

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

theorem NarrowDNF.HatamiCrossTerms.bMass_mul_inactiveKernel_le {p k δ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (A : Finset (Finset ι)) (a m : Finset ι → ℝ)
    (ham : ∀ S ∈ A, a S ≤ m S) (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k)
    (T : Finset ι) :
    bMass A a T * inactiveKernel p (thresholdActivation k p δ A m) T ≤ (2:ℝ)^T.card * δ := by sorry
