-- Prove2me | Theorems.Thm_GlobalTheory_Serre_finrank_fractionalIdeal
-- name    : GlobalTheory.Serre.finrank_fractionalIdeal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:09.54464+00:00
-- url     : https://prove2.me/theorems/671daad1-799d-46a4-ad58-9aaefae397f5
-- title:
--   Serre: finrank fractional Ideal
-- statement:
--   The Serre construction uses the finrank fractional Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L215-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L215-L225

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
omit [CharZero k] [NumberField K]

theorem GlobalTheory.Serre.finrank_fractionalIdeal {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    Module.finrank (𝓞 E) I = 1 := by sorry
