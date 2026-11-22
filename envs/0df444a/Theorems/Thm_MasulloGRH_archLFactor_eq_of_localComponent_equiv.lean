-- Prove2me | Theorems.Thm_MasulloGRH_archLFactor_eq_of_localComponent_equiv
-- name    : MasulloGRH.archLFactor_eq_of_localComponent_equiv
-- status  : Proved
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:29:05.740705+00:00
-- url     : https://prove2.me/theorems/7030ae20-751d-40ee-ae57-95ae93c8acdb
-- title:
--   Archimedean Hecke factors are invariant under transport of local characters
-- statement:
--   Consider two infinite places of number fields of the same real or complex type. Suppose an isomorphism between their completions intertwines their chosen embeddings in $\mathbb C$, possibly up to complex conjugation. If two Hecke characters have matching local components under this isomorphism, then their archimedean local $L$-factors agree as functions of the complex variable. Conjugation preserves the exponent on positive reals and negates the integer weight on the circle, so it preserves the absolute weight used in the Gamma factor.
-- source:
--   Invariance of the local factors in A. M. Masullo, The Music of the Primes, Definition 3.2.1.2, equations (3.2.1.4)–(3.2.1.5), p. 123, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=123. Sublemma of https://prove2.me/theorems/cd82016f-759b-4356-918c-9555c4133271.

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped WithZero

namespace MasulloGRH

theorem archLFactor_eq_of_localComponent_equiv
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (ψ : HeckeCharacter K) (v : InfinitePlace F) (w : InfinitePlace K)
    (a : v.Completion ≃+* w.Completion)
    (hreal : v.IsReal ↔ w.IsReal)
    (hemb : ∃ conjugate : Bool, ∀ x : v.Completion,
      InfinitePlace.Completion.extensionEmbedding w (a x) =
        if conjugate then star (InfinitePlace.Completion.extensionEmbedding v x)
        else InfinitePlace.Completion.extensionEmbedding v x)
    (hlocal : ∀ x : (v.Completion)ˣ,
      χ.localComponentInfinite v x = ψ.localComponentInfinite w (Units.map a.toMonoidHom x)) :
    χ.archLFactor v = ψ.archLFactor w := by
  sorry

end MasulloGRH
