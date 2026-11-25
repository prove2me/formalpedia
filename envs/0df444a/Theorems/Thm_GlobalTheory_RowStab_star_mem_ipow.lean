-- Prove2me | Theorems.Thm_GlobalTheory_RowStab_star_mem_ipow
-- name    : GlobalTheory.RowStab.star_mem_ipow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:29:21.481573+00:00
-- url     : https://prove2.me/theorems/adf987f6-11b2-5e46-ae95-d981d96085a9
-- title:
--   Row Stab: star mem ipow
-- statement:
--   The Row Stab construction uses the star mem ipow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L129-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean#L129-L149

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem GlobalTheory.RowStab.star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) {x : K} (hx : x ∈ ipow 𝔡 n) :
    star x ∈ ipow 𝔡 n := by sorry
