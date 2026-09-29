-- Prove2me | Theorems.Thm_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
-- name    : Ideal.exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/9044f430-f669-5675-abbf-6c0adc05b933
-- title:
--   Completion along a minimal prime when the completion is a domain
-- statement:
--   Let $S$ be a commutative Noetherian ring, let $\mathfrak q$ be an ideal of $S$ lying in $\mathrm{minimalPrimes}\ S$, i.e. a minimal member of the set of prime ideals of $S$ (the minimal primes of the zero ideal), let $x$ be a maximal ideal of $S$ with $\mathfrak q \le x$, and assume that the $x$-adic completion $\mathrm{AdicCompletion}\ x\ S$, the inverse limit of the rings $S/x^n$, is an integral domain. Then there is a ring isomorphism $e$ from the adic completion of $S/\mathfrak q$ with respect to the image ideal $x \cdot (S/\mathfrak q)$, namely `x.map (Ideal.Quotient.mk 𝔮)`, onto $\mathrm{AdicCompletion}\ x\ S$, which is compatible with the quotient map in the following sense: for every $s \in S$, the image under $e$ of the canonical image of $s \bmod \mathfrak q$ in the completion of $S/\mathfrak q$ equals the canonical image of $s$ in $\mathrm{AdicCompletion}\ x\ S$. The isomorphism is asserted to exist together with this compatibility; no canonical choice is produced.
--
--   This says that if a Noetherian ring has integral $x$-adic completion, then passing to the quotient by a minimal prime contained in $x$ does not change that completion — the completion sees a single branch. It is used in the analysis of completed local rings of moduli of elliptic curves with level structure, where the completion of an irreducible component at a point is identified with the completion of the ambient ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (𝔮 : Ideal S) (h𝔮 : 𝔮 ∈ minimalPrimes S)
    (x : Ideal S) [x.IsMaximal] (hle : 𝔮 ≤ x)
    (hdom : IsDomain (AdicCompletion x S)) :
    ∃ e : AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮) ≃+* AdicCompletion x S,
      ∀ s : S, e (algebraMap (S ⧸ 𝔮) (AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮)) (Ideal.Quotient.mk 𝔮 s)) =
        algebraMap S (AdicCompletion x S) s := by sorry
