-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_hasNormalPComplement_of_isNilpotent
-- name    : OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:21.472816+00:00
-- url     : https://prove2.me/theorems/5c86671a-f770-49e5-88e5-4c06fca2e990
-- title:
--   A finite nilpotent group has a normal $p$-complement for every prime $p$
-- statement:
--   Let $H$ be a finite nilpotent group and $p$ a prime. Then $H$ has a normal $p$-complement: there is a normal subgroup $N\trianglelefteq H$ which is a complement to every Sylow $p$-subgroup of $H$.
--
--   The complement is the kernel of the projection of the Sylow direct-product decomposition of $H$ onto its $p$-component. This is used in the proof of Isaacs Thm 6.24 (Isaacs p. 196).
--
--   **Formalization Note** `HasNormalPComplement p H` is the project definition: $\exists N\trianglelefteq H$, $\forall P\in\mathrm{Syl}_p(H)$, `Subgroup.IsComplement' N P`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/NilpotentPComplement.lean#L124-L181

import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Mathlib.GroupTheory.Nilpotent

namespace OddOrder.Isaacs.Ch05

open scoped Pointwise

section

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem hasNormalPComplement_of_isNilpotent [Group.IsNilpotent H] :
    HasNormalPComplement p H := by sorry

end

end OddOrder.Isaacs.Ch05
