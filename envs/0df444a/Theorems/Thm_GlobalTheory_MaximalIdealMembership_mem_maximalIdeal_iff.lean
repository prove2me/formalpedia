-- Prove2me | Theorems.Thm_GlobalTheory_MaximalIdealMembership_mem_maximalIdeal_iff
-- name    : GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:21:13.643441+00:00
-- url     : https://prove2.me/theorems/000daec7-a42e-4543-8500-32efa376d1e9
-- title:
--   Maximal Ideal Membership: mem maximal Ideal iff
-- statement:
--   The Maximal Ideal Membership construction uses the mem maximal Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Imports.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Imports.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealMembership

theorem GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by sorry
