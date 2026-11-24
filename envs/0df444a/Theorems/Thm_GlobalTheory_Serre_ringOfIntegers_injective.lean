-- Prove2me | Theorems.Thm_GlobalTheory_Serre_ringOfIntegers_injective
-- name    : GlobalTheory.Serre.ringOfIntegers_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:27.178804+00:00
-- url     : https://prove2.me/theorems/e50c0fb5-9c7c-4e2c-b088-ae92af6205ad
-- title:
--   Serre: ring Of Integers injective
-- statement:
--   The Serre construction uses the ring Of Integers injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L192-L196

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
omit [NumberField K]

theorem GlobalTheory.Serre.ringOfIntegers_injective (τ : 𝓞 K →+* k) : Function.Injective τ := by sorry
