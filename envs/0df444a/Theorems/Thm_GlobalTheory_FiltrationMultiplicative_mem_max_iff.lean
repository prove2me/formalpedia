-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_mem_max_iff
-- name    : GlobalTheory.FiltrationMultiplicative.mem_max_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:18.986995+00:00
-- url     : https://prove2.me/theorems/f0c8ab26-9fdb-4225-95c3-2644623f3a1a
-- title:
--   Filtration Multiplicative: mem max iff
-- statement:
--   The Filtration Multiplicative construction uses the mem max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.FiltrationMultiplicative.mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ↔
      coeff 0 f ∈ IsLocalRing.maximalIdeal O := by sorry
