-- Prove2me | Theorems.Thm_MasulloGRH_exists_ideleClassEquiv_and_localEquivs_of_ringEquiv
-- name    : MasulloGRH.exists_ideleClassEquiv_and_localEquivs_of_ringEquiv
-- status  : Proved
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:28:52.417523+00:00
-- url     : https://prove2.me/theorems/59a1f091-6195-48ad-abe6-7f937f19da8b
-- title:
--   Transport of idele classes and local completions under a number field isomorphism
-- statement:
--   Let $e:F\cong K$ be an isomorphism of number fields. The induced bijection on finite places comes from the isomorphism of rings of integers. There are a topological group isomorphism on idele classes, a bijection on infinite places, and ring isomorphisms between the corresponding local completions. At finite places the local maps preserve the normalized valuations. At infinite places they preserve the real or complex type and intertwine the chosen embeddings into $\mathbb C$ up to complex conjugation, with a fixed choice at each place. The idele class isomorphism commutes with each map that inserts a local unit at one place.
-- source:
--   Transport of the local data used in A. M. Masullo, The Music of the Primes, §3.2.1, pp. 122–124, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=123. Sublemma of https://prove2.me/theorems/cd82016f-759b-4356-918c-9555c4133271.

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped WithZero

namespace MasulloGRH

theorem exists_ideleClassEquiv_and_localEquivs_of_ringEquiv
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    (e : F ≃+* K) :
    let p := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)
    ∃ (c : IdeleClassGroup F ≃ₜ* IdeleClassGroup K)
      (w : InfinitePlace F ≃ InfinitePlace K)
      (finite : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F ≃+* (p v).adicCompletion K)
      (infinite : ∀ v : InfinitePlace F, v.Completion ≃+* (w v).Completion),
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v (finite v x) = (Valued.v x : ℤᵐ⁰)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ),
        c (QuotientGroup.mk (ideleSingle v x)) =
          QuotientGroup.mk (ideleSingle (p v) (Units.map (finite v).toMonoidHom x))) ∧
      (∀ v : InfinitePlace F, v.IsReal ↔ (w v).IsReal) ∧
      (∀ v : InfinitePlace F, ∃ conjugate : Bool, ∀ x : v.Completion,
        InfinitePlace.Completion.extensionEmbedding (w v) (infinite v x) =
          if conjugate then star (InfinitePlace.Completion.extensionEmbedding v x)
          else InfinitePlace.Completion.extensionEmbedding v x) ∧
      (∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
        c (QuotientGroup.mk (ideleSingleInfinite v x)) =
          QuotientGroup.mk (ideleSingleInfinite (w v) (Units.map (infinite v).toMonoidHom x))) := by
  sorry

end MasulloGRH
