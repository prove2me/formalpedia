-- Prove2me | Theorems.Thm_GlobalTheory_LatFibre_fibreMap_injective
-- name    : GlobalTheory.LatFibre.fibreMap_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:58.988956+00:00
-- url     : https://prove2.me/theorems/00417fa5-08b2-43fa-a1ff-a063880d5e5e
-- title:
--   Lat Fibre: fibre Map injective
-- statement:
--   The Lat Fibre construction uses the fibre Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivLatticeClassesFibreSummand.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivLatticeClassesFibreSummand.lean#L43-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.LatFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LatFibre.fibreMap_injective (𝔞 𝔟 : Frac F) : Function.Injective (fibreMap 𝔞 𝔟) := by sorry
