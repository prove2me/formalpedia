-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_not_cdom_add_root
-- name    : GlobalTheory.CompanionTheory.DSHighestOfKType.not_cdom_add_root
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:32.499715+00:00
-- url     : https://prove2.me/theorems/544ddd18-d604-4c20-9d6d-e7603e376064
-- title:
--   DSHighest Of KType: not cdom add root
-- statement:
--   The DSHighest Of KType construction uses the not cdom add root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L17-L40

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSHighestOfKType.not_cdom_add_root (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + root a b) μ := by sorry
