-- Prove2me | Theorems.Thm_GlobalTheory_RowStab_ipow_mul_mem
-- name    : GlobalTheory.RowStab.ipow_mul_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:54.579908+00:00
-- url     : https://prove2.me/theorems/1827a7c9-b030-4fc0-af10-b7db97573236
-- title:
--   Row Stab: ipow mul mem
-- statement:
--   The Row Stab construction uses the ipow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L27-L33

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

theorem GlobalTheory.RowStab.ipow_mul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m)
    (hy : y ∈ ipow 𝔡 n) : x * y ∈ ipow 𝔡 (m + n) := by sorry
