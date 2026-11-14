-- Prove2me | Theorems.Thm_NarrowDNF_BourgainNoise_finite_positive_fourth_contraction
-- name    : NarrowDNF.BourgainNoise.finite_positive_fourth_contraction
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:08:46.356209+00:00
-- url     : https://prove2.me/theorems/184f2792-5215-4be4-bb7c-cdb1cb56c386
-- title:
--   Fourth-moment contraction for positive mean noise
-- statement:
--   Let \(\alpha\) be finite, let \(w_x\ge0\) be probability weights with \(\sum_xw_x=1\), and let \(f:\alpha\to\mathbb R\). Define the weighted mean \(a=\sum_xw_xf_x\). Shrinking the deviation from that mean by a factor of three contracts the fourth moment:
--   $$\sum_xw_x\left(a+\frac{f_x-a}{3}\right)^4\le\sum_xw_xf_x^4.$$
--   This finite-space positive-noise estimate applies to any real observable, without restrictions on its sign or the number of points. It provides the positive counterpart of the negative-noise contraction for subsequent tensorization.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L67-L90

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainNoise
end NarrowDNF.BourgainNoise

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
open NarrowDNF.BourgainNoise

theorem NarrowDNF.BourgainNoise.finite_positive_fourth_contraction {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    (∑ x, w x * ((∑ y, w y * f y) + (f x - ∑ y, w y * f y) / 3) ^ 4) ≤
      ∑ x, w x * f x ^ 4 := by sorry
