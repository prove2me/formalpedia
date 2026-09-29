-- Prove2me | Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
-- name    : NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3ae17bad-36f6-5e41-8773-6828069fcc13
-- title:
--   Cyclic p-power subfield of E(ζ_{p^k}) with large local degrees
-- statement:
--   Let $E$ be a number field, let $T$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_E$, let $p$ be a prime and let $a$ be a natural number. The assertion is that there exist a natural number $k$ and a number field $F'$, equipped with an $E$-algebra structure making $F'/E$ Galois and the group $F' \simeq_{\mathrm{alg}[E]} F'$ of $E$-automorphisms cyclic, such that five conditions hold simultaneously: (i) there exists an $E$-algebra homomorphism $F' \to \mathrm{CyclotomicField}(p^k, E)$, i.e. $F'$ embeds over $E$ into $E(\zeta_{p^k})$; (ii) for every infinite place $w$ of $F'$, every $g$ in the stabiliser of $w$ for the action of the Galois group on infinite places (the subgroup [`NumberField.InfPlaceDecomp.decomp`](def/NumberField_ArchimedeanIdeleModule.html#L23)) is the identity, so all these decomposition groups are trivial; (iii) $p^a$ divides $\#\mathrm{Gal}(F'/E)$; (iv) for every $v \in T$ and every height-one prime $w$ of $\mathcal{O}_{F'}$ whose contraction to $\mathcal{O}_E$ is $v$, the quantity $p^a$ divides the cardinality of the decomposition subgroup of the valuation subring attached to $w$ (the subgroup [`NumberField.PlaceDecomp.decomp`](def/NumberField_PlaceDecompositionAction.html#L82)); and (v) $\mathrm{Gal}(F'/E)$ is a $p$-group.
--
--   This is the one-prime case of Artin's lemma on auxiliary cyclic cyclotomic extensions with prescribed local degrees, in the form needed later: a cyclic $p$-power extension inside a $p$-power cyclotomic field, unramified (indeed with trivial decomposition groups) at the infinite places, and with local degrees at the chosen finite places divisible by $p^a$. It feeds the Herbrand-type averaging computation over decomposition groups and the construction of suitably ramified Galois extensions used in the level arithmetic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain

theorem NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsCyclic (F' ≃ₐ[E] F')),
      Nonempty (F' →ₐ[E] CyclotomicField (p ^ k) E) ∧
      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧
      p ^ a ∣ Nat.card (F' ≃ₐ[E] F') ∧
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        p ^ a ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) ∧

      IsPGroup p (F' ≃ₐ[E] F') := by sorry
