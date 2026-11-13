-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S14_theorem88_dichotomy
-- name    : OddOrder.Peterfalvi.S14.theorem88_dichotomy
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:27:32.382124+00:00
-- url     : https://prove2.me/theorems/1fecb3b1-f494-430d-b7a7-65b60bcf4f64
-- title:
--   Peterfalvi (8.8) dichotomy: all maximal subgroups type I, or case-(b) pairing data exist
-- statement:
--   Let $G$ be a finite group which is a minimal simple group of odd order (`OddOrder.BG.IsMinimalSimpleOdd G`). Then one of the following holds:
--
--   - every maximal subgroup $M$ of $G$ is of type I (`IsTypeI M`); or
--   - the case-(b) pairing data of Peterfalvi (8.8) exist: `Nonempty (Theorem88CaseBData G)`.
--
--   This is the dichotomy of Peterfalvi Theorem (8.8) (BG Section 16): a maximal subgroup that is not of type I is of type P, and the type-P duality produces the case-(b) pairing data.
--
--   **Formalization Note.** `maximalSubgroups G` is the set of maximal subgroups; `Theorem88CaseBData` is a project structure.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean#L493-L594

import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_NormPackage
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem theorem88_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S10.Theorem88CaseBData G) := by sorry

end OddOrder.Peterfalvi.S14
