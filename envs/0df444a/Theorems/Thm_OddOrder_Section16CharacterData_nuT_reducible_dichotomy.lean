-- Prove2me | Theorems.Thm_OddOrder_Section16CharacterData_nuT_reducible_dichotomy
-- name    : OddOrder.Section16CharacterData.nuT_reducible_dichotomy
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:53:53.716715+00:00
-- url     : https://prove2.me/theorems/985d4b01-5830-4fd0-9ee8-2e7a6ad524ef
-- title:
--   Peterfalvi (9.8)/(9.11): a reducible member of the kernel-filter family on $T'$ is a $\nu$-row sum
-- statement:
--   In the Section 16 setting, let $G$ be a finite group which is a minimal simple group of odd order (`hG : IsMinimalSimpleOdd G`), let `mp : Section16MaximalPair G` be a pair of maximal subgroups, with $T=$ `mp.T`, and let `tp : Section16TypePStructure mp` be a type P structure with primes $p=$ `tp.p`, $q=$ `tp.q` (the relevant $W_1$ groups having nonzero order). Let $X\le T$ be a subgroup and $\psi$ a class function on $T$ which belongs to the kernel-filter family `inducedKernelFamily (T'.subgroupOf T) X` over $T'$ (the derived subgroup of $T$). If $\psi$ is not an irreducible character, then there is $i\in\mathrm{Fin}\,q$ with $i\ne0$ such that
--   $$\psi=\sum_{j\in\mathrm{Fin}\,p}\nu_{ij},$$
--   where $\nu_{ij}=$ `nuT hG mp tp i j`.
--
--   That is, every reducible member of the family is a non-anchor canonical $\nu$-row sum. This is the $T$-side reverse dichotomy of Peterfalvi (9.8)/(9.11).
--
--   **Formalization Note** `inducedKernelFamily`, `nuT`, and the Section 16 structures are project-specific; characters are `ClassFunction ↥mp.T ℂ`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonNuGrid.lean#L521-L565

import Definitions.Def_OddOrder_FeitThompsonSetup
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_FeitThompsonNuGrid

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
  (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

theorem nuT_reducible_dichotomy {X : Subgroup ↥mp.T} {ψ : ClassFunction ↥mp.T ℂ}
    (hψ : ψ ∈ Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.T).subgroupOf mp.T) X)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ ∧
      ψ = ∑ j : Fin tp.p, nuT hG mp tp i j := by sorry

end Section16CharacterData

end

end OddOrder
