-- Prove2me | Theorems.Thm_NarrowDNF_HatamiInput_paper_truncation_error_le
-- name    : NarrowDNF.HatamiInput.paper_truncation_error_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:56:28.406385+00:00
-- url     : https://prove2.me/theorems/454d62e9-ed81-42c3-bd0f-c4f9d7c62711
-- title:
--   Paper-parameter squared error after Fourier pruning
-- statement:
--   Let $I$ be finite, $0<p<1$, $0<a\le1$, and Boolean $f$ satisfy total resampling influence $I_p(f)\le C$ for an integer $C\ge1$. Set $e=a/1000$, $k=1000C/a$, $\eta=3^{-10k^2}e^{10k}$, and retain $\mathcal A=\{S:|S|\le k,\ \|F_S\|_\infty>\eta\}$, where $F_S$ are the Fourier components of the $0/1$ encoding of $f$. Then
--   $$E_p\left[\left(f-\sum_{S\in\mathcal A}F_S\right)^2\right]\le2a/1000.$$
--   This combines the high-degree and small-component pruning losses at the source parameters.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiInput.lean#L58-L94

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainEstimate_paper_smallComponentMass_bound
import Theorems.Thm_NarrowDNF_FourierTruncation_significant_remainder_le
import Theorems.Thm_NarrowDNF_HatamiInput_highDegreeReal_mass_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiInput.paper_truncation_error_le {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (HatamiResidual.truncated p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))) ≤
            2*(a/1000) := by sorry
