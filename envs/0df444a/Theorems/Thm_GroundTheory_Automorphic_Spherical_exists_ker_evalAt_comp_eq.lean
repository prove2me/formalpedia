-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_exists_ker_evalAt_comp_eq
-- name    : GroundTheory.Automorphic.Spherical.exists_ker_evalAt_comp_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:40.023838+00:00
-- url     : https://prove2.me/theorems/b14c523d-4b9c-491b-8de6-dffaf7ce6d76
-- title:
--   Spherical: exists ker eval At comp eq
-- statement:
--   The Spherical construction uses the exists ker eval At comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L112-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L112-L145

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.exists_ker_evalAt_comp_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    (Φ : A →ₐ[ℂ] LaurentRing n) (hΦ : Function.Injective Φ)
    [hint : Algebra.IsIntegral Φ.range (LaurentRing n)] (I : Ideal A) [hI : I.IsMaximal] :
    ∃ w : Fin n → ℂˣ, RingHom.ker ((evalAt w).comp Φ) = I := by sorry
