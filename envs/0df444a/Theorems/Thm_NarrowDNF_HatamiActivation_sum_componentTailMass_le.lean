-- Prove2me | Theorems.Thm_NarrowDNF_HatamiActivation_sum_componentTailMass_le
-- name    : NarrowDNF.HatamiActivation.sum_componentTailMass_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:49.850869+00:00
-- url     : https://prove2.me/theorems/312ff051-b522-487c-81aa-106c6708c37b
-- title:
--   The total retained Fourier-component tail mass is at most the inverse squared threshold
-- statement:
--   Let \(I\) be finite, \(0<p<1\), \(\eta>0\), and \(f:\{0,1\}^I\to\{0,1\}\), with Boolean values interpreted numerically as zero and one. Let \(\mathcal R\) be any family of coordinate subsets. For \(S\subseteq I\), let \(\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\), \(\widehat f_p(S)=\mathbb E_p[f\chi_S^p]\), \(f_S=\widehat f_p(S)\chi_S^p\), and \(b_S=\Pr_p(|f_S(X)|\ge\eta)\). Then
--   $$\sum_{S\in\mathcal R}b_S\le\eta^{-2}.$$
--   This bound is independent of the size, overlap, or distribution of the retained supports, providing a uniform mass budget for activation constructions.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L372-L390

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
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_HatamiActivation_probability_abs_ge_le_sq

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

theorem NarrowDNF.HatamiActivation.sum_componentTailMass_le {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (f : Cube ι → Bool) (retained : Finset (Finset ι)) :
    (∑ S ∈ retained, componentTailMass p (fun x => Influence.boolValue (f x)) η S) ≤
      1 / η^2 := by sorry
