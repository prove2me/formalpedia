-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_gam_eq
-- name    : GlobalTheory.CompanionTheory.GamDomProof.gam_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:31.340152+00:00
-- url     : https://prove2.me/theorems/182b7afc-91a6-46b6-9984-4baa3675e70a
-- title:
--   Gam Dom Proof: gam eq
-- statement:
--   The Gam Dom Proof construction uses the gam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CardOther.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CardOther.lean#L83-L94

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CardOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open CompanionTheory.D.DSIC
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GamDomProof
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.GamDomProof.gam_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by sorry
