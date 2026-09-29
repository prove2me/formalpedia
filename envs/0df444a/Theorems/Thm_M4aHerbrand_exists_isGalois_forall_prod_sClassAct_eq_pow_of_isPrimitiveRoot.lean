-- Prove2me | Theorems.Thm_M4aHerbrand_exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
-- name    : M4aHerbrand.exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e0b58be1-5e29-525f-a897-5d50a03d8aeb
-- title:
--   An S-ramified existence theorem for S-idèle class groups
-- statement:
--   Let $E$ be a number field, $p$ a prime, and $\zeta \in E$ a primitive $p$-th root of unity; let $S$ be a finite set of rational primes with $p \in S$. The assertion is that there exist a number field $F$ carrying an $E$-algebra structure, finite-dimensional and Galois over $E$, together with an idèle Galois descent datum $D$ for $F/E$ — a monoid homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adèle ring of $\mathcal{O}_F$ over $F$, each automorphism continuous, and compatible with the action on $F$ through the structure map — whose induced action on units stabilises the subgroup `unitIdelesTrivialOn` attached to the set $T =$ `placesOverPrimes F S` of height-one primes $w$ of $\mathcal{O}_F$ containing some rational prime of $S$, i.e. the intersection of the unit idèles outside $T$ with the idèles trivial on $T$. For this $F$ and $D$ two things hold: first, every height-one prime $w$ of $\mathcal{O}_F$ not in $T$ satisfies $\mathrm{ramificationIdx}'$ equal to $1$ over the prime of $\mathcal{O}_E$ it contracts to; second, for every class $c$ in the $S$-idèle class group $(\mathbb{A}_F^\times)/(\text{principal idèles} \sqcup \text{unitIdelesTrivialOn } T)$ there is a class $d$ in that same group, fixed by `sClassAct` for every $g \in F \simeq_{\mathrm{alg}[E]} F$, with $\prod_{g} (\mathrm{sClassAct}\, g)(c) = d^{\,p}$, the product being the (finite) product over the Galois group.
--
--   This is the existence theorem of global class field theory in $S$-ramified, single-module norm form: the Galois norm on the $S$-idèle class group of a suitable extension lands in $p$-th powers of Galois-invariant classes. It feeds the Herbrand-quotient estimates through [`IntermediateField.exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow`](thm.html#IntermediateField.exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow), which transports the conclusion to an intermediate field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem M4aHerbrand.exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
    (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset Nat.Primes) (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra E F) (_ : FiniteDimensional E F) (_ : IsGalois E F)
      (D : IdeleGaloisDescent (𝓞 F) E F) (hD : D.StabilizesUnitIdeles (NumberField.placesOverPrimes F (↑S : Set Nat.Primes))),
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ NumberField.placesOverPrimes F (↑S : Set Nat.Primes) →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) ∧
      ∀ c : SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)),
        ∃ d : SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)),
          (∀ g : F ≃ₐ[E] F, D.sClassAct hD g d = d) ∧
          (∏ᶠ g : F ≃ₐ[E] F, D.sClassAct hD g c) = d ^ p := by sorry
