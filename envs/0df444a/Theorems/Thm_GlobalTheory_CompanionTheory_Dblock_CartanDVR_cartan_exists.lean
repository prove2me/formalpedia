-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CartanDVR_cartan_exists
-- name    : GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:27.441112+00:00
-- url     : https://prove2.me/theorems/df72c1c0-0c66-48b9-b5f7-8f313c3205d4
-- title:
--   Cartan DVR: cartan exists
-- statement:
--   The Cartan DVR construction uses the cartan exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanExists.lean#L8-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanExists.lean#L8-L75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CartanDVR
open Matrix

theorem GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by sorry
