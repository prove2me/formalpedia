-- Prove2me | Theorems.Thm_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite
-- name    : HenselianLocalRing.moduleFinite_localizationAtPrime_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/da0fa0a2-1203-56bf-b63a-c35021f6c6d1
-- title:
--   Finiteness of localisations of a finite algebra over a henselian base
-- statement:
--   Let $A$ be a commutative ring which is local and henselian, and let $B$ be a commutative $A$-algebra which is finite as an $A$-module. Let $\mathfrak n$ be an ideal of $B$ that is maximal. The assertion is that the localisation of $B$ at the prime $\mathfrak n$, that is `Localization.AtPrime 𝔫` (the localisation of $B$ at the multiplicative set $B \setminus \mathfrak n$), is again finite as an $A$-module, the $A$-module structure being the one obtained from $A \to B \to B_{\mathfrak n}$. No separatedness, flatness or Noetherian hypothesis on $B$ is imposed, and $\mathfrak n$ ranges over all maximal ideals of $B$; the conclusion is finiteness as an $A$-module, which is stronger than finite generation over the local ring $A$ of the residue data alone.
--
--   This is the henselian splitting principle in the form: over a henselian local base, a finite algebra decomposes as a product of local rings, so each of its localisations at a maximal ideal is itself a finite module over the base. It serves as the henselian input in the proof of [`HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated`](thm.html#HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated) and of [`HenselianLocalRing.moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors`](thm.html#HenselianLocalRing.moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors), where it combines with Zariski's main theorem to promote quasi-finiteness to finiteness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.moduleFinite_localizationAtPrime_of_moduleFinite
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.Finite A (Localization.AtPrime 𝔫) := by sorry
