-- Prove2me | Theorems.Thm_GlobalTheory_Serre_formallyUnramified_ringOfIntegers
-- name    : GlobalTheory.Serre.formallyUnramified_ringOfIntegers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:21.627651+00:00
-- url     : https://prove2.me/theorems/64769f1d-6a29-4391-af84-70ab64380582
-- title:
--   Serre: formally Unramified ring Of Integers
-- statement:
--   The Serre construction uses the formally Unramified ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L198-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L198-L211

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

theorem GlobalTheory.Serre.formallyUnramified_ringOfIntegers [Algebra (𝓞 K) k] :
    Algebra.FormallyUnramified k (k ⊗[𝓞 K] 𝓞 E) := by sorry
