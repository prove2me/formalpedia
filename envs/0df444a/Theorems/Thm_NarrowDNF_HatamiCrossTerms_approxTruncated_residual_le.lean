-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_approxTruncated_residual_le
-- name    : NarrowDNF.HatamiCrossTerms.approxTruncated_residual_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:49:55.963797+00:00
-- url     : https://prove2.me/theorems/bd7d3110-52dd-4c84-bdcf-2033742b02a5
-- title:
--   Step III residual bound with the corrected cross-term exponent
-- statement:
--   Let $f:\{0,1\}^I\to\{0,1\}$ on finite $I$, $0<p\le1/2$, $k\ge1$, $0\le\delta\le1$, and $\eta>0$. Write $F_S$ for its biased Fourier components, $\mathcal A=\{S:|S|\le k,\ \|F_S\|_\infty>\eta\}$, and $J$ for the threshold activation built from tail masses $P_p(|F_S|\ge\eta)$. Let $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$, where $J_S$ retains activations inside $S$. Define $M=\sum_{|S|\le k}E_p[F_S^2\mathbf1_{|F_S|\le\eta}]$. Then
--   $$E_p\left[\left(\sum_{S\in\mathcal A}(F_S-\widetilde F_S)\right)^2\right]\le2kM+2^{9k}\delta/\eta^2.$$
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L463-L513

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
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_corrected
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_residual_le_rank_factor
import Theorems.Thm_NarrowDNF_HatamiResidual_sum_diagonal_le_small_mass

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

theorem NarrowDNF.HatamiCrossTerms.approxTruncated_residual_le {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hk : 1 ≤ k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (f : Cube ι → Bool) :
    ConditionalExpectation.squaredError (weight p)
      (truncated p (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η))
      (approxTruncated p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
        (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η)) ≤
      2*k*FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k η +
        (2:ℝ)^(9*k)*δ/η^2 := by sorry
