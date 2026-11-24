-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSCoreSub_algCoreSub_of_algCore
-- name    : GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:29.497021+00:00
-- url     : https://prove2.me/theorems/5afc471a-54b5-49e7-941c-287d9b232abd
-- title:
--   DSCore Sub: alg Core Sub of alg Core
-- statement:
--   The DSCore Sub construction uses the alg Core Sub of alg Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L32-L55

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AlgCoreSubOfAlgCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCoreSub
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore : AlgCore → AlgCoreSub := by sorry
