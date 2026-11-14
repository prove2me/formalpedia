-- Prove2me | Theorems.Thm_NarrowDNF_BourgainEstimate_smallComponentMass_le_general
-- name    : NarrowDNF.BourgainEstimate.smallComponentMass_le_general
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:48:55.774342+00:00
-- url     : https://prove2.me/theorems/779be5c2-c992-41d3-8a12-b927822f79a5
-- title:
--   Bourgain small-component estimate with auxiliary parameters
-- statement:
--   Let \(\iota\) be finite, \(0<p<1\), and let \(f:\{0,1\}^{\iota}\to\{0,1\}\). Under Bernoulli measure \(\mu_p\), define \(\chi_S(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\) and \(f_S(x)=\mathbb E_p[f\chi_S]\chi_S(x)\). Let \(k\in\mathbb N\), positive integer \(M\), real \(\eta\), \(\tau>0\), and \(C\ge0\) satisfy \(I_p(f)\le C\), where \(I_p\) is total independent-resampling influence. Then
--   $$\mathbb E_p\sum_{|S|\le k}f_S(x)^2\mathbf1_{|f_S(x)|\le\eta}\le M^k\eta^2+2C3^{2k}\tau^{2/3}+\frac{3^{2k}\sqrt C}{\sqrt M\,\tau}.$$
--   This leaves the counting and square-function thresholds available for later optimization.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainEstimate.lean#L19-L68

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_BourgainDuality
import Definitions.Def_NarrowDNF_BourgainSquareFunction
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainIntegration_integrated_bourgain_split
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_fourth
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_squareFunction_moment43
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction

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
open NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainEstimate.smallComponentMass_le_general {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k M : ℕ) (hM : 0 < M) (η τ C : ℝ)
    (hτ : 0 < τ) (hC0 : 0 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k η ≤
      (M : ℝ)^k * η^2 + 2*C*(3 : ℝ)^(2*k)*τ^(2/3 : ℝ) +
        (3 : ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (M : ℝ)*τ) := by sorry
