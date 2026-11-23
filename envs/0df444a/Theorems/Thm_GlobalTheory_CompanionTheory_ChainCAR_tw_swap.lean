-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_tw_swap
-- name    : GlobalTheory.CompanionTheory.ChainCAR.tw_swap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:28.095974+00:00
-- url     : https://prove2.me/theorems/95d2dad2-7960-4f7d-b7ea-2da0ec107727
-- title:
--   Chain CAR: tw swap
-- statement:
--   The Chain CAR construction uses the tw swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L33-L38

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.ChainCAR.tw_swap {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j := by sorry
