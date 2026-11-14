-- Prove2me | Theorems.Thm_NarrowDNF_HatamiActivation_localMass_le_componentTailMass
-- name    : NarrowDNF.HatamiActivation.localMass_le_componentTailMass
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:15.545003+00:00
-- url     : https://prove2.me/theorems/6de16750-1f40-4712-9072-0781cb9d4505
-- title:
--   A realized component-tail event dominates its local assignment mass
-- statement:
--   Let \(I\) be finite, \(0\le p\le1\), \(f:\{0,1\}^I\to\mathbb R\), \(\eta\in\mathbb R\), and \(S\subseteq I\). Write \(\chi_S^p(u)=\prod_{i\in S}\frac{u_i-p}{\sqrt{p(1-p)}}\) and \(f_S=\mathbb E_p[f\chi_S^p]\chi_S^p\), with division by zero assigned value zero. Define
--   $$L_{p,S}(x)=\prod_{i\in S}p^{x_i}(1-p)^{1-x_i},\qquad b_S=\Pr_p(|f_S(X)|\ge\eta).$$
--   If an input \(x\) satisfies \(|f_S(x)|\ge\eta\), then
--   $$L_{p,S}(x)\le b_S.$$
--   No positivity assumption on \(\eta\) or strict interior-bias assumption is required. This connects a tail event actually realized by a local assignment to its total event mass.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L273-L293

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

theorem NarrowDNF.HatamiActivation.localMass_le_componentTailMass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) (x : Cube ι)
    (hx : η ≤ |Fourier.component p f S x|) :
    localMass p S x ≤ componentTailMass p f η S := by sorry
