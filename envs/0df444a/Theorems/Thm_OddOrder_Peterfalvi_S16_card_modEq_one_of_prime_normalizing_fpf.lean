-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_card_modEq_one_of_prime_normalizing_fpf
-- name    : OddOrder.Peterfalvi.S16.card_modEq_one_of_prime_normalizing_fpf
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:26:16.981569+00:00
-- url     : https://prove2.me/theorems/7e40221c-fc12-4bb9-9c04-6df820ab3959
-- title:
--   Fixed-point-free congruence: a subgroup of prime order $p$ acting fixed-point-freely on $U$ gives $|U|\equiv1\pmod p$
-- statement:
--   Let $G$ be a finite group, $U$ and $A$ subgroups of $G$, and $p$ a prime. Assume $|A|=p$, $A$ normalizes $U$ (`A ≤ normalizer U`), and $A$ acts on $U$ fixed-point-freely by conjugation: for all $a\in A\setminus\{1\}$ and $u\in U\setminus\{1\}$,
--   $$a u a^{-1}\neq u .$$
--   Then
--   $$|U|\equiv 1 \pmod p .$$
--
--   The $p$-group $A$ acts on $U$ with $\{1\}$ as its only fixed point, so the fixed-point congruence for $p$-group actions gives $|U|\equiv 1\pmod p$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean#L499-L541

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem card_modEq_one_of_prime_normalizing_fpf {G : Type*} [Group G] [Finite G]
    {U A : Subgroup G} {p : ℕ} (hp : p.Prime) (hA_card : Nat.card ↥A = p)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ U, u ≠ 1 → (a : G) * u * (a : G)⁻¹ ≠ u) :
    Nat.card ↥U ≡ 1 [MOD p] := by sorry

end OddOrder.Peterfalvi.S16
