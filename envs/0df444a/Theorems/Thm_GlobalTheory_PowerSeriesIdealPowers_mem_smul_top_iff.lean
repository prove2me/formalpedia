-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_smul_top_iff
-- name    : GlobalTheory.PowerSeriesIdealPowers.mem_smul_top_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:50.099387+00:00
-- url     : https://prove2.me/theorems/c93a7ec6-a63d-4d08-9a45-a220ea998696
-- title:
--   Power Series Ideal Powers: mem smul top iff
-- statement:
--   The Power Series Ideal Powers construction uses the mem smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.PowerSeriesIdealPowers.mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by sorry
