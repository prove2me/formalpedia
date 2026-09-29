-- Prove2me | Theorems.Thm_M4aHerbrand_ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd
-- name    : M4aHerbrand.ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/b8a1f422-9900-51ab-a32d-719de6727623
-- title:
--   First inequality: [F:E] divides #̂ H⁰(C_F)
-- statement:
--   Let $E \subseteq F$ be number fields (in arbitrary universes) with $F/E$ Galois and with cyclic Galois group $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$, let $D$ be a Galois descent datum for the adeles of $F$ over $E$, that is, a monoid homomorphism $\mathrm{Gal}(F/E) \to \mathrm{RingAut}(\mathbb{A}_F)$ into the ring automorphisms of the adele ring of $F$ over $\mathcal{O}_F$, each of whose values is continuous and restricts along $F \to \mathbb{A}_F$ to the given action on $F$, and let $\sigma$ be an element of $\mathrm{Gal}(F/E)$ such that every $\tau$ lies in the subgroup of integral powers of $\sigma$. Write $C_F$ for the idele class group $\mathbb{A}_F^\times / \mathrm{principalIdeles}$, on which $D$ induces an action of $\mathrm{Gal}(F/E)$ by group automorphisms; let $\mathrm{ideleClassDerive}\,D\,\sigma$ be the endomorphism $c \mapsto (\sigma \cdot c)\,c^{-1}$ of $C_F$ and $\mathrm{ideleClassNorm}\,D$ the endomorphism $c \mapsto \prod_{\tau \in \mathrm{Gal}(F/E)} \tau \cdot c$. The assertion is about the quotient of $\ker(\mathrm{ideleClassDerive}\,D\,\sigma)$ by the subgroup of that kernel consisting of the elements lying in the image of $\mathrm{ideleClassNorm}\,D$: its `Nat.card` is nonzero, i.e. the quotient is finite, and the degree $[F:E] = \mathrm{finrank}_E F$ divides that cardinality.
--
--   This is the first inequality of global class field theory in its Tate-cohomological form: for cyclic $F/E$ the group $\hat H^0(\mathrm{Gal}(F/E), C_F) = \ker(\sigma - 1)/N_{F/E} C_F$ is finite of order divisible by $[F:E]$. It feeds, together with the computation of the Herbrand quotient from the $S$-unit, finite-idele and infinite-idele contributions, into [`NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime`](thm.html#NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime) and hence into the class field theory underlying the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand

theorem M4aHerbrand.ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (σ : F ≃ₐ[E] F) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card ((ideleClassDerive D σ).ker ⧸
      ((ideleClassNorm D).range.subgroupOf (ideleClassDerive D σ).ker)) ≠ 0 ∧
    Module.finrank E F ∣
    Nat.card ((ideleClassDerive D σ).ker ⧸
      ((ideleClassNorm D).range.subgroupOf (ideleClassDerive D σ).ker)) := by sorry
