-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S14_exists_typeICovering
-- name    : OddOrder.Peterfalvi.S14.exists_typeICovering
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:41:45.722333+00:00
-- url     : https://prove2.me/theorems/7406f024-b3db-4105-9aca-2a174f973ccb
-- title:
--   Peterfalvi (8.17)/(8.13.c1): existence of the type-I covering data in the all-type-I case
-- statement:
--   Let $G$ be a finite group which is a minimal simple group of odd order (`OddOrder.BG.IsMinimalSimpleOdd G`). Assume that no maximal subgroup of $G$ is of type V and that every maximal subgroup of $G$ is of type I. Then the covering data `TypeICovering hG hall` exist:
--   $$\texttt{Nonempty}\ (\texttt{TypeICovering}\ hG\ hall).$$
--
--   This provides the Section 8 covering inputs of Peterfalvi (12.17) in the all-type-I case, obtained from the BG Theorem E covering data.
--
--   **Formalization Note.** `TypeICovering` is a project structure bundling representatives of conjugacy classes of maximal subgroups and their coprimality and covering properties; it is described only by name here.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean#L239-L426

import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_NormPackage
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section Theorem1217

variable [Finite G]

theorem exists_typeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by sorry

end Theorem1217

end OddOrder.Peterfalvi.S14
