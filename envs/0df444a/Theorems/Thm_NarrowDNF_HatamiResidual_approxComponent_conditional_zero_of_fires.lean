-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_conditional_zero_of_fires
-- name    : NarrowDNF.HatamiResidual.approxComponent_conditional_zero_of_fires
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:48.435226+00:00
-- url     : https://prove2.me/theorems/fc61162e-096c-41df-9cc7-0e7d54e04007
-- title:
--   Vanishing conditional component on a fired proper sub-support
-- statement:
--   Let $I$ be finite, $0<p<1$, $J$ a local activation family, and $f$ real valued. Suppose $T\subseteq S$ but $S\nsubseteq T$, and $J$ fires $T$ at an input $x_0$. Let $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$. The coordinate-fiber average satisfies
--   $$E_p[\widetilde F_S\mid x|_T=x_0|_T]=0.$$
--   Here $J_S$ retains the original activations indexed inside $S$. The result is the fired-overlap cancellation used when estimating products of components on distinct supports.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L579-L612

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
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_residual_orthogonal
import Theorems.Thm_NarrowDNF_HatamiResidual_component_conditional_zero
import Theorems.Thm_NarrowDNF_HatamiResidual_fired_fiber_indicator_measurable

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

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiResidual
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiResidual.approxComponent_conditional_zero_of_fires {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S T : Finset ι) (hTS : T ⊆ S)
    (hST : ¬ S ⊆ T) (x0 : Cube ι) (hfire : J.fires T x0) :
    ConditionalExpectation.mean (restriction T) (weight p) (approxComponent p J f S)
      (restriction T x0) = 0 := by sorry
