-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_dl_comm
-- name    : GlobalTheory.CompanionTheory.DSICFRel.dl_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:46.930484+00:00
-- url     : https://prove2.me/theorems/a699032d-7f8b-4630-8393-f098d8612515
-- title:
--   DSICFRel: dl comm
-- statement:
--   The DSICFRel construction uses the dl comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L89-L90

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

theorem GlobalTheory.CompanionTheory.DSICFRel.dl_comm (x y : Fin n) : dl x y = dl y x := by sorry
