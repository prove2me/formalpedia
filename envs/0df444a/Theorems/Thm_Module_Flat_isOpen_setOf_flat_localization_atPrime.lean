-- Prove2me | Theorems.Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime
-- name    : Module.Flat.isOpen_setOf_flat_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/a5a9fcb9-99d9-5caf-9727-1e71e77eaa2a
-- title:
--   Openness of the flat locus for finite type algebras
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and assume $A$ is Noetherian and $B$ is of finite type over $A$. Consider the subset of the prime spectrum of $B$ consisting of those primes $Q$ whose associated prime ideal $Q.asIdeal$ has the property that the localisation of $B$ at that prime is flat as an $A$-module, the $A$-module structure being the one induced through $B$. The assertion is that this subset is open in the Zariski topology on $\operatorname{Spec} B$. Note that flatness is taken over $A$ of the local ring $B_Q$ regarded as an $A$-module, not of $B$ itself; no hypothesis of finiteness on $B$ as an $A$-module, and no Noetherian hypothesis on $B$ beyond what finite type over a Noetherian $A$ gives, is imposed.
--
--   This is the Noetherian case of the openness of the flat locus of a morphism of finite type, EGA IV 11.1.1 (Matsumura, Theorem 24.3). Within this development it is used to produce flatness over suitable finitely generated subalgebras, via [`Module.Flat.exists_fg_subalgebra_flat_tensorProduct`](thm.html#Module.Flat.exists_fg_subalgebra_flat_tensorProduct) and in the faithful flatness statement [`HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed); the proof combines generic flatness ([`Module.Flat.exists_ne_zero_flat_localization_tensorProduct`](thm.html#Module.Flat.exists_ne_zero_flat_localization_tensorProduct)) with the local criterion [`Module.flat_of_comap_maximalIdeal_rTensor_injective`](thm.html#Module.flat_of_comap_maximalIdeal_rTensor_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.Flat.isOpen_setOf_flat_localization_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} := by sorry
