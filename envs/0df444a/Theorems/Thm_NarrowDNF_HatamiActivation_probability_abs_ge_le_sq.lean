-- Prove2me | Theorems.Thm_NarrowDNF_HatamiActivation_probability_abs_ge_le_sq
-- name    : NarrowDNF.HatamiActivation.probability_abs_ge_le_sq
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:03.92861+00:00
-- url     : https://prove2.me/theorems/da34be99-f98f-463d-8100-8b0409a4ccc2
-- title:
--   The squared Markov bound for an absolute-value tail
-- statement:
--   Let \(I\) be finite, \(0\le p\le1\), \(\eta>0\), and \(F:\{0,1\}^I\to\mathbb R\). For Bernoulli product probability and expectation,
--   $$\Pr_p(|F(X)|\ge\eta)\le\frac{\mathbb E_p[F(X)^2]}{\eta^2}.$$
--   The event uses a non-strict comparison at the threshold. The assertion permits the degenerate endpoint biases \(p=0\) and \(p=1\), because only nonnegative product weights are needed. It is the second-moment tail estimate used for individual Fourier components.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L348-L363

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

theorem NarrowDNF.HatamiActivation.probability_abs_ge_le_sq {p η : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hη : 0 < η) (F : Cube ι → ℝ) :
    probability p (fun x => η ≤ |F x|) ≤ expectation p (fun x => (F x)^2) / η^2 := by sorry
