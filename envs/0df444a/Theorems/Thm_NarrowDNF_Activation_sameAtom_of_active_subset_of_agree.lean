-- Prove2me | Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
-- name    : NarrowDNF.Activation.sameAtom_of_active_subset_of_agree
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:24.843556+00:00
-- url     : https://prove2.me/theorems/90daf531-ec30-4bdb-a479-0e507356ee53
-- title:
--   Recovery of an adaptive atom from a common coordinate set
-- statement:
--   Let \(\iota\) be a coordinate set and \(J\) an activation family whose test on every finite set \(S\) depends only on the coordinates in \(S\). For an input \(z\), let \(A_J(z)\) be the union of all sets whose tests fire. Suppose \(x,y\in\{0,1\}^{\iota}\) and \(B\subseteq\iota\) satisfy
--   $$A_J(x)\subseteq B,\qquad A_J(y)\subseteq B,\qquad x_i=y_i\ \text{for every }i\in B.$$
--   Then \(x\) and \(y\) belong to the same adaptive atom:
--   $$A_J(x)=A_J(y),\qquad x_i=y_i\ \text{for every }i\in A_J(x).$$
--   This recovers the full adaptive information from labels on any common superset of the active unions.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/AdaptiveShift.lean#L40-L64

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation
open NarrowDNF
variable {ι : Type*} [DecidableEq ι]
open NarrowDNF
open NarrowDNF.Activation
omit [DecidableEq ι]

theorem NarrowDNF.Activation.sameAtom_of_active_subset_of_agree {J : Activation ι} {x y : Cube ι}
    {B : Set ι} (hx : J.active x ⊆ B) (hy : J.active y ⊆ B)
    (hxy : ∀ i ∈ B, x i = y i) : J.SameAtom x y := by sorry
