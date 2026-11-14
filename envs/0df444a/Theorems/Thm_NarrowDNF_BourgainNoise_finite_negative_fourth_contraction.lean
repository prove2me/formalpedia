-- Prove2me | Theorems.Thm_NarrowDNF_BourgainNoise_finite_negative_fourth_contraction
-- name    : NarrowDNF.BourgainNoise.finite_negative_fourth_contraction
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:08:42.033895+00:00
-- url     : https://prove2.me/theorems/a3301ad1-c43e-424e-880a-605601b6bddb
-- title:
--   Fourth-moment contraction for negative mean noise
-- statement:
--   Let \(\alpha\) be finite, let \(w_x\ge0\) satisfy \(\sum_xw_x=1\), and let \(f:\alpha\to\mathbb R\). Write \(a=\sum_xw_xf_x\) for its weighted mean. The negative-noise transform \(f_x\mapsto a-(f_x-a)/3\) satisfies
--   $$\sum_xw_x\left(a-\frac{f_x-a}{3}\right)^4\le\sum_xw_xf_x^4.$$
--   Thus reflecting the centered part and shrinking it by a factor of three contracts the fourth moment on every finite probability space. This supplies the negative one-coordinate estimate used in tensorized signed-noise bounds. Zero individual weights are allowed throughout.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L41-L65

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

theorem NarrowDNF.BourgainNoise.finite_negative_fourth_contraction {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    (∑ x, w x * ((∑ y, w y * f y) - (f x - ∑ y, w y * f y) / 3) ^ 4) ≤
      ∑ x, w x * f x ^ 4 := by sorry
