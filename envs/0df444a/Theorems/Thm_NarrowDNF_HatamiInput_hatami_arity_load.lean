-- Prove2me | Theorems.Thm_NarrowDNF_HatamiInput_hatami_arity_load
-- name    : NarrowDNF.HatamiInput.hatami_arity_load
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T09:02:34.029801+00:00
-- url     : https://prove2.me/theorems/33ebf2f6-4cab-4de2-819b-fae9c8e5e8ea
-- title:
--   Hatami's simultaneous approximation, arity, and load theorem
-- statement:
--   For every $n\in\mathbb N$, $0<p\le1/2$, Boolean $f:\{0,1\}^n\to\{0,1\}$, and $0<a\le1$, set $C=\lceil I_p(f)\rceil$, where $I_p$ is total independent-resampling influence. There exist a local activation family $J$ and Boolean $h$ such that $J$ is increasing, $h$ is constant on the adaptive atoms of $J$, and
--   $$P_p(f\ne h)\le a,\qquad\operatorname{arity}(J)\le\left\lceil1000C/a\right\rceil,\qquad\operatorname{load}_p(J)\le\exp(10^{10}C^2/a^2).$$
--   An adaptive atom records the active coordinates and their actual input values. The theorem provides all approximation and complexity bounds simultaneously, as required by Lemma 2.1.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiInput.lean#L237-L259

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
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiInput
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_squaredError_decomposition
import Theorems.Thm_NarrowDNF_Fourier_eq_mean_of_variance_le_zero
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_Fourier_variance_le_spectralEnergy
import Theorems.Thm_NarrowDNF_HatamiActivation_sum_componentTailMass_le
import Theorems.Thm_NarrowDNF_HatamiActivation_threshold_load_le
import Theorems.Thm_NarrowDNF_HatamiInput_paper_approxTruncated_error_le
import Theorems.Thm_NarrowDNF_HatamiInput_paper_truncation_error_le
import Theorems.Thm_NarrowDNF_HatamiParameters_loadExpression_le_exp
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

namespace NarrowDNF.HatamiParameters
end NarrowDNF.HatamiParameters

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiInput.hatami_arity_load : NarrowDNF.HatamiArityLoad := by sorry
