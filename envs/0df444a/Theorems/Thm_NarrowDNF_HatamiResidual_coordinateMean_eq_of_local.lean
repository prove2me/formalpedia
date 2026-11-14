-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_coordinateMean_eq_of_local
-- name    : NarrowDNF.HatamiResidual.coordinateMean_eq_of_local
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:06.112198+00:00
-- url     : https://prove2.me/theorems/85ec22ee-aec9-491e-a802-93d40a1c293d
-- title:
--   Averaging an unread coordinate fixes a local function
-- statement:
--   Let $I$ be a coordinate type with decidable equality, $T\subseteq I$ finite, and $G:\{0,1\}^I\to\mathbb R$ depend only on the coordinates in $T$: agreement on $T$ implies equal values of $G$. For any real $p$, any $i\notin T$, and any input $x$,
--   $$(1-p)G(x^{i\leftarrow0})+pG(x^{i\leftarrow1})=G(x).$$
--   No finiteness assumption on the whole coordinate type is needed. The expression is the one-coordinate averaging operator, interpreted probabilistically when $0\le p\le1$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L395-L410

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
omit [Fintype ι]

theorem NarrowDNF.HatamiResidual.coordinateMean_eq_of_local (p : ℝ) (T : Finset ι) (G : Cube ι → ℝ)
    (hG : ∀ x y, (∀ j ∈ T, x j = y j) → G x = G y) (i : ι) (hi : i ∉ T)
    (x : Cube ι) : Fourier.coordinateMean p G i x = G x := by sorry
