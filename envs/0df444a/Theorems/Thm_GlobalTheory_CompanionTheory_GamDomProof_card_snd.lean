-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_card_snd
-- name    : GlobalTheory.CompanionTheory.GamDomProof.card_snd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:44.043733+00:00
-- url     : https://prove2.me/theorems/0aedf07c-d930-49f8-977b-c798b2fc8b8a
-- title:
--   Gam Dom Proof: card snd
-- statement:
--   The Gam Dom Proof construction uses the card snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CardOther.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CardOther.lean#L49-L71

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

theorem GlobalTheory.CompanionTheory.GamDomProof.card_snd (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.2 = a).card =
      if ε a = true then 0 else (univ.filter fun b => a < b ∧ ε b ≠ ε a).card := by sorry
