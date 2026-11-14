-- Prove2me | Theorems.Thm_NarrowDNF_HatamiActivation_threshold_probability_le
-- name    : NarrowDNF.HatamiActivation.threshold_probability_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:21.080202+00:00
-- url     : https://prove2.me/theorems/25a69e98-2dcd-4c0e-8d02-9f614c83d069
-- title:
--   Firing weight of one threshold activation
-- statement:
--   On a finite Boolean cube, let $p,k\in\mathbb R$, $\delta>0$, and let a finite family $\mathcal A$ carry masses $m_S\ge0$. For $T\subseteq I$, define $b_T=\sum_{S\in\mathcal A,\,T\subseteq S}m_S$ and its marginal product weight $w_{p,T}(x)$. Let $J_T(x)$ mean $|T|\le k$ and $\delta w_{p,T}(x)\le b_T$. With $P_p$ denoting the finite product-weight event sum,
--   $$P_p(J_T)\le\frac{2^{|T|}b_T}{\delta}.$$
--   The formal statement allows every real $p$; for $0\le p\le1$, this is the usual Bernoulli event probability.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L117-L135

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

theorem NarrowDNF.HatamiActivation.threshold_probability_le {k p δ : ℝ} (hδ : 0 < δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (T : Finset ι) :
    probability p ((thresholdActivation k p δ retained m).fires T) ≤
      (2 : ℝ)^T.card * bMass retained m T / δ := by sorry
