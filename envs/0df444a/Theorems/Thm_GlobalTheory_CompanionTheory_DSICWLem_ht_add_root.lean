-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICWLem_ht_add_root
-- name    : GlobalTheory.CompanionTheory.DSICWLem.ht_add_root
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:59.96402+00:00
-- url     : https://prove2.me/theorems/f60a0380-cd7b-435d-aec6-18267308f324
-- title:
--   DSICWLem: ht add root
-- statement:
--   The DSICWLem construction uses the ht add root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WlemOfGfacts.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WlemOfGfacts.lean#L16-L23

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WlemOfGfacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICWLem
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

theorem GlobalTheory.CompanionTheory.DSICWLem.ht_add_root {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by sorry
