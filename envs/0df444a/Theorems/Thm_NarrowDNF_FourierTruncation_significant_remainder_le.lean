-- Prove2me | Theorems.Thm_NarrowDNF_FourierTruncation_significant_remainder_le
-- name    : NarrowDNF.FourierTruncation.significant_remainder_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:32.849311+00:00
-- url     : https://prove2.me/theorems/8ceeaf04-42ff-4173-9785-0784c022616e
-- title:
--   The significant-component truncation error splits into high degree and small components
-- statement:
--   Let \(I\) be finite, \(0<p<1\), \(f:\{0,1\}^I\to\mathbb R\), and \(k,\eta\in\mathbb R\). Write \(f_S(x)=\widehat f_p(S)\chi_S^p(x)\), and retain
--   $$\mathcal R=\{S:|S|\le k,\ \exists x\;|f_S(x)|>\eta\}.$$
--   Define the small-component energy by
--   $$B=\sum_S\mathbb E_p[\mathbf1_{\{|S|\le k,\ |f_S(X)|\le\eta\}}f_S(X)^2].$$
--   Then
--   $$\mathbb E_p\!\left[\left(f-\sum_{S\in\mathcal R}f_S\right)^2\right]\le\sum_{|S|>k}\widehat f_p(S)^2+B.$$
--   The cutoffs may be arbitrary real numbers. This separates two error sources before inserting any quantitative high-degree or Bourgain estimate.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FourierTruncation.lean#L65-L96

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
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.FourierTruncation
end NarrowDNF.FourierTruncation

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open NarrowDNF
open NarrowDNF.FourierTruncation
open ProductMeasure Fourier
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.FourierTruncation.significant_remainder_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (k η : ℝ) :
    ConditionalExpectation.squaredError (weight p) f
      (partialSum p f (HatamiActivation.significantSets p f k η)) ≤
      (∑ S : Finset ι, if k < (S.card : ℝ) then setCoefficient p f S ^ 2 else 0) +
        smallMassReal p f k η := by sorry
