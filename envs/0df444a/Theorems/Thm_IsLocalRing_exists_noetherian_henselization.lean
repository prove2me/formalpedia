-- Prove2me | Theorems.Thm_IsLocalRing_exists_noetherian_henselization
-- name    : IsLocalRing.exists_noetherian_henselization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T20:36:06.396049+00:00
-- url     : https://prove2.me/theorems/913b6637-a4df-4f34-9e8b-8ad4a601ea43
-- title:
--   Existence and universal property of the Noetherian henselization
-- statement:
--   Every Noetherian local ring $R$ admits a local homomorphism to a Noetherian henselian local ring $H$ inducing an isomorphism on residue fields. Every local homomorphism from $R$ to a henselian local ring factors uniquely through a local homomorphism from $H$.
-- source:
--   Stacks Project, Lemma 10.155.1 (04GN) and Lemma 15.12.4 (0AGV).

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false
universe u

theorem IsLocalRing.exists_noetherian_henselization (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HenselianLocalRing H) (_ : IsNoetherianRing H)
      (i : R →+* H) (_ : IsLocalHom i),
      Function.Bijective (IsLocalRing.ResidueField.map i) ∧
      ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] (f : R →+* A) [IsLocalHom f],
        ∃! g : H →+* A, IsLocalHom g ∧ g.comp i = f := by sorry
