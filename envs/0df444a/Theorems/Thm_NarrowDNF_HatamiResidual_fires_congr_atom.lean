-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_fires_congr_atom
-- name    : NarrowDNF.HatamiResidual.fires_congr_atom
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:43.340065+00:00
-- url     : https://prove2.me/theorems/1628c4d2-c6a7-4969-9c0c-cb5d46eeba3c
-- title:
--   Firing status is constant on an activation family’s adaptive atoms
-- statement:
--   Let $J$ be a local activation family on a Boolean cube, and let $T$ be any finite coordinate set. Two inputs $x,y$ belong to the same adaptive atom when their active coordinate sets coincide and their values agree on that set. Then
--   $$J_T(x)\quad\Longleftrightarrow\quad J_T(y).$$
--   Here $J_T$ denotes firing of the activation indexed by $T$, whose truth depends only on coordinates in $T$. The ambient coordinate type need not be finite. The result ensures that firing events can be read from the adaptive partition itself.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L60-L74

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

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

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

theorem NarrowDNF.HatamiResidual.fires_congr_atom (J : Activation ι) (T : Finset ι) {x y : Cube ι}
    (hxy : J.SameAtom x y) : J.fires T x ↔ J.fires T y := by sorry
