-- Prove2me | Theorems.Thm_GlobalTheory_SlopeTestRemainingChoices_EisFibre_rep_mem
-- name    : GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:14.838818+00:00
-- url     : https://prove2.me/theorems/1ecce92e-1c14-4f7f-9cf8-e9ddc79d0fd3
-- title:
--   Eis Fibre: rep mem
-- statement:
--   The Eis Fibre construction uses the rep mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepNeZero.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepNeZero.lean#L27-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SlopeTestRemainingChoices GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep_mem {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by sorry
