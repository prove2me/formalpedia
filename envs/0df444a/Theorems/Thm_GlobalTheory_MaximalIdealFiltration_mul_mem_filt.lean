-- Prove2me | Theorems.Thm_GlobalTheory_MaximalIdealFiltration_mul_mem_filt
-- name    : GlobalTheory.MaximalIdealFiltration.mul_mem_filt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:54.004719+00:00
-- url     : https://prove2.me/theorems/50ac2437-e8ac-4638-ac3f-39ceb8b5194f
-- title:
--   Maximal Ideal Filtration: mul mem filt
-- statement:
--   The Maximal Ideal Filtration construction uses the mul mem filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MaximalIdealLeFiltOne.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MaximalIdealLeFiltOne.lean#L29-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem GlobalTheory.MaximalIdealFiltration.mul_mem_filt {k l : ℕ} {f g : MvPowerSeries (Fin a) O}
    (hf : f ∈ filt (O := O) k) (hg : g ∈ filt (O := O) l) : f * g ∈ filt (O := O) (k + l) := by sorry
