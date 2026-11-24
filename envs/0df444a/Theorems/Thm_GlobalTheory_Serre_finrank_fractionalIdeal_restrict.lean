-- Prove2me | Theorems.Thm_GlobalTheory_Serre_finrank_fractionalIdeal_restrict
-- name    : GlobalTheory.Serre.finrank_fractionalIdeal_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:23.901124+00:00
-- url     : https://prove2.me/theorems/375a9380-6f28-44fa-adfa-f08656085710
-- title:
--   Serre: finrank fractional Ideal restrict
-- statement:
--   The Serre construction uses the finrank fractional Ideal restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L229-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L229-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
open NumberField
variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
omit [CharZero k]

theorem GlobalTheory.Serre.finrank_fractionalIdeal_restrict {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (hI : I ≠ 0) : Module.finrank (𝓞 K) I = Module.finrank K E := by sorry
