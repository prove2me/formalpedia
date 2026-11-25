-- Prove2me | Theorems.Thm_GlobalTheory_RowStab_mem_ipow_of_mul
-- name    : GlobalTheory.RowStab.mem_ipow_of_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:56.147204+00:00
-- url     : https://prove2.me/theorems/7e1eeef6-9be1-5449-a616-0d91f26cb220
-- title:
--   Row Stab: mem ipow of mul
-- statement:
--   The Row Stab construction uses the mem ipow of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L46-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
open GlobalTheory GlobalTheory.RowStab
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.RowStab.mem_ipow_of_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (h : ∀ t ∈ ipow 𝔡 (-m), t * x ∈ ipow 𝔡 n) : x ∈ ipow 𝔡 (m + n) := by sorry
