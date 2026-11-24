-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_ann_ann
-- name    : GlobalTheory.CompanionTheory.ChainCAR.ann_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:40.746269+00:00
-- url     : https://prove2.me/theorems/fed0e72e-75cb-4d8c-8d7d-0db2be977100
-- title:
--   Chain CAR: ann ann
-- statement:
--   The Chain CAR construction uses the ann ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreApply.lean#L66-L81

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ChainCAR.ann_ann (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 := by sorry
