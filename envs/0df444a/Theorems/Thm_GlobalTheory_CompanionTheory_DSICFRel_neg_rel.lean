-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_neg_rel
-- name    : GlobalTheory.CompanionTheory.DSICFRel.neg_rel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:40.280794+00:00
-- url     : https://prove2.me/theorems/ac87ceaa-6e6d-4183-9c7c-a0ed42c0e426
-- title:
--   DSICFRel: neg rel
-- statement:
--   The DSICFRel construction uses the neg rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L187-L194

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSICFRel.neg_rel {A : Type} [Ring A] (ε : Fin n → Bool) (G : Fin n → Fin n → A) (hG : KRel ε G) :
    KRel ε (fun c d => -G d c) := by sorry
