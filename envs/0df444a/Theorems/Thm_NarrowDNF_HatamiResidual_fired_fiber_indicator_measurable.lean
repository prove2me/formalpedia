-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_fired_fiber_indicator_measurable
-- name    : NarrowDNF.HatamiResidual.fired_fiber_indicator_measurable
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:13.434373+00:00
-- url     : https://prove2.me/theorems/b4961f5c-05d5-4d32-92ec-56d1d25ab884
-- title:
--   A fired coordinate fiber is measurable for the restricted adaptive partition
-- statement:
--   Let $J$ be a local activation family, $T\subseteq S$ finite coordinate sets, and suppose $J$ fires $T$ at $x_0$. Let $J_S$ retain just the activations indexed inside $S$. If $x$ and $y$ lie in the same $J_S$-adaptive atom, then
--   $$\mathbf1_{\{x|_T=x_0|_T\}}=\mathbf1_{\{y|_T=x_0|_T\}}.$$
--   The indicator takes real values $0$ and $1$. This is the precise measurability statement needed to test a conditional-expectation residual against a fired fiber; it preserves the actual revealed coordinate values.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L554-L577

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
import Definitions.Def_NarrowDNF_HatamiResidual
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
omit [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiResidual.fired_fiber_indicator_measurable (J : Activation ι) (S T : Finset ι)
    (hTS : T ⊆ S) (x0 : Cube ι) (hfire : J.fires T x0) (x y : Cube ι)
    (hxy : (restrict J S).SameAtom x y) :
    (if restriction T x = restriction T x0 then (1:ℝ) else 0) =
      (if restriction T y = restriction T x0 then 1 else 0) := by sorry
