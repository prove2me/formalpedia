-- Prove2me | Theorems.Thm_OddOrder_Section16CharacterData_muS_reducible_dichotomy
-- name    : OddOrder.Section16CharacterData.muS_reducible_dichotomy
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:47:08.273459+00:00
-- url     : https://prove2.me/theorems/fb534475-b2e5-4892-8f0c-517c15bc434a
-- title:
--   Peterfalvi (9.8)/(9.11): a reducible member of the kernel-filter family on $S'$ is a $\mu$-column sum
-- statement:
--   In the Section 16 setting, let $G$ be a finite group which is a minimal simple group of odd order (`hG : IsMinimalSimpleOdd G`), let `mp : Section16MaximalPair G` be a pair of maximal subgroups with $S=$ `mp.S`, and let `tp : Section16TypePStructure mp` be a type P structure with primes $p=$ `tp.p`, $q=$ `tp.q` (the relevant $W_1$ group having nonzero order). Let $X\le S$ be a subgroup and $\psi$ a class function on $S$ in the kernel-filter family `inducedKernelFamily (S'.subgroupOf S) X` over $S'$ (the derived subgroup of $S$). If $\psi$ is not an irreducible character, then there is $j\in\mathrm{Fin}\,p$ with $j\ne0$ such that
--   $$\psi=\sum_{i\in\mathrm{Fin}\,q}\mu_{ij},$$
--   where $\mu_{ij}=$ `muS hG mp tp i j`.
--
--   That is, every reducible member is a nonzero $\mu$-column sum. This is the $S$-instance of the reverse dichotomy of Peterfalvi (9.8)/(9.11).
--
--   **Formalization Note** `inducedKernelFamily`, `muS`, and the Section 16 structures are project-specific.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonSetup.lean#L303-L351

import Definitions.Def_OddOrder_FeitThompsonSection16Core
import Definitions.Def_OddOrder_FeitThompsonSetup

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

set_option backward.isDefEq.respectTransparency false in

theorem muS_reducible_dichotomy {X : Subgroup ↥mp.S} {ψ : ClassFunction ↥mp.S ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.S).subgroupOf mp.S) X)
    (hred : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ) :
    ∃ j : Fin tp.p, j ≠ ⟨0, tp.p_prime.pos⟩ ∧ ψ = ∑ i : Fin tp.q, muS hG mp tp i j := by sorry

end Section16CharacterData

end

end OddOrder
