-- Prove2me | Theorems.Thm_NumberField_PrimeNormIndex_ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime
-- name    : NumberField.PrimeNormIndex.ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/b05ad8a0-aaab-5967-8818-cb1743f86686
-- title:
--   Second inequality at prime degree: ̂ H⁰ of idele classes
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra such that $F/E$ is Galois, let $p$ be a prime and assume $\operatorname{finrank}_E F = p$. Let $D$ be an idele Galois descent datum for $\mathcal{O}_F$ over $E$ and $F$, that is, a monoid homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adele ring $\mathbb{A}_F$, each automorphism continuous, and compatible with the structure map in the sense that $D.\mathrm{act}\,\tau$ sends the image of $x \in F$ to the image of $\tau x$. Write $C_F = \mathbb{A}_F^{\times}/\mathrm{principalIdeles}$ for the idele class group, on which $D$ induces an action by `classAct`; let `ideleClassNorm D` be the endomorphism $c \mapsto \prod_{\tau} \tau \cdot c$ of $C_F$, the product over all $E$-automorphisms of $F$, and for $\sigma$ an $E$-automorphism of $F$ let `ideleClassDerive D σ` be the endomorphism $c \mapsto (\sigma \cdot c)\,c^{-1}$. The assertion is: for every $\sigma$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, the cardinality of the quotient of $\ker(\mathrm{ideleClassDerive}\ D\ \sigma)$ by the subgroup of it cut out by the range of `ideleClassNorm D` divides $p$. Since `Nat.card` is $0$ for an infinite group and $0$ does not divide a prime, this includes the finiteness of that quotient.
--
--   This is the second inequality of global class field theory in the prime-degree case: for $\sigma$ a generator of the cyclic group $\mathrm{Gal}(F/E)$ the kernel of $c \mapsto (\sigma \cdot c)c^{-1}$ is the group of Galois-invariant idele classes, so the quotient in question is the Tate group $\hat H^0(\mathrm{Gal}(F/E), C_F)$, whose order is asserted to divide $p$. It is used, together with the matching lower bound, in [`NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime`](thm.html#NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime) to pin down the Herbrand-quotient data for a cyclic extension of prime degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PrimeNormIndex_ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.PrimeNormIndex.ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [IsGalois E F] (p : ℕ) (hp : p.Prime) (hdeg : Module.finrank E F = p)
    (D : M4aHerbrand.IdeleGaloisDescent (NumberField.RingOfIntegers F) E F) :
    ∀ σ : F ≃ₐ[E] F, (∀ τ, τ ∈ Subgroup.zpowers σ) →
      Nat.card ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        ((M4aHerbrand.ideleClassNorm D).range.subgroupOf
          (M4aHerbrand.ideleClassDerive D σ).ker)) ∣ p := by sorry
