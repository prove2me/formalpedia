-- Prove2me | Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
-- name    : NarrowDNF.ConditionalExpectation.adaptiveCode_eq_iff
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:10:52.909314+00:00
-- url     : https://prove2.me/theorems/eaba9c70-8f25-4019-a3c1-c42d603b058c
-- title:
--   The finite adaptive code identifies exactly the adaptive atoms
-- statement:
--   Let \(I\) be finite and \(J\) a local activation family: whether a subset \(S\) fires depends only on the input coordinates in \(S\). For an input \(x\), let \(A_J(x)\) be the union of all firing subsets. Define \(z_J(x)\) to equal \(x\) on \(A_J(x)\) and zero outside it, and encode the input as \(c_J(x)=(A_J(x),z_J(x))\). For all inputs \(x,y\),
--   $$c_J(x)=c_J(y)\iff A_J(x)=A_J(y)\ \text{and}\ x|_{A_J(x)}=y|_{A_J(x)}.$$
--   Thus this finite code realizes exactly the adaptive partition specified by the active set and its observed labels.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L255-L282

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem NarrowDNF.ConditionalExpectation.adaptiveCode_eq_iff (J : Activation ι) (x y : Cube ι) :
    adaptiveCode J x = adaptiveCode J y ↔ J.SameAtom x y := by sorry
