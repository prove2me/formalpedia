-- Prove2me | Theorems.Thm_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite
-- name    : HenselianLocalRing.isLocalRing_of_isDomain_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d340d885-9800-5441-b0f1-808d5e486725
-- title:
--   A domain module-finite over a henselian local ring is local
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, and let $S$ be a commutative ring which is an integral domain, equipped with an $R$-algebra structure under which $S$ is finite as an $R$-module. The conclusion is that $S$ is a local ring, i.e. `IsLocalRing S` holds: $S$ is nontrivial and possesses a unique maximal ideal (equivalently, the non-units of $S$ are closed under addition). No separability, flatness or Noetherian hypothesis on $R$ or on the extension is imposed; finiteness of $S$ as an $R$-module and absence of zero divisors in $S$ are the only assumptions beyond henselianity of $R$. In particular the statement covers the classical case of the integral closure of a henselian valuation ring inside a finite extension of its fraction field.
--
--   This is the standard fact that a henselian local ring has no splitting in finite domain extensions: the uniqueness of the extension of the local structure (and hence, in the valuation-theoretic case, of the valuation) to a finite extension. Within this development it serves the analysis of valuation subrings with henselian localisations, being used by [`ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing`](thm.html#ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing), [`ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap`](thm.html#ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap) and [`ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing`](thm.html#ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by sorry
