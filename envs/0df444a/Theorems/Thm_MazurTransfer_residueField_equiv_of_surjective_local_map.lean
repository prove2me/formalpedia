-- Prove2me | Theorems.Thm_MazurTransfer_residueField_equiv_of_surjective_local_map
-- name    : MazurTransfer.residueField_equiv_of_surjective_local_map
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T11:55:59.604993+00:00
-- url     : https://prove2.me/theorems/c5ec0dd1-e629-4a8a-8006-d9c0b7f050f8
-- title:
--   Residue field from a surjective local map
-- statement:
--   Let $R$ be a commutative local ring and $k$ a field. Let $\pi:R\to k$ be a surjective ring homomorphism such that $\pi(r)=0$ if and only if $r$ is a nonunit of $R$. There is a ring isomorphism $\kappa(R)\simeq k$ whose composite with the residue map is $\pi$. Thus a specified local residue map determines the residue field while preserving its values on the original ring.
-- source:
--   Original elementary residue-field proof developed in the MazurTheorem integration, https://github.com/Vilin97/MazurTheorem, using Mathlib quotient maps and injectivity of field homomorphisms. Named local application: the original decomposition-fixed henselian valuation ring above13 has residue field F13 through the SAME official residue map.

import Mathlib

theorem MazurTransfer.residueField_equiv_of_surjective_local_map (R k : Type) [CommRing R] [IsLocalRing R] [Field k]
    (π : R →+* k) (hs : Function.Surjective π)
    (hπ : ∀ r : R, π r = 0 ↔ ¬ IsUnit r) :
    ∃ e : IsLocalRing.ResidueField R ≃+* k,
      ∀ r : R, e (IsLocalRing.residue R r) = π r := by sorry
