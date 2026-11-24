-- Prove2me | Theorems.Thm_GlobalTheory_LocalRingBasicFacts_main
-- name    : GlobalTheory.LocalRingBasicFacts.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:13:55.020806+00:00
-- url     : https://prove2.me/theorems/adc39501-a5dc-435c-aa25-12c87c491270
-- title:
--   Local Ring Basic Facts: main
-- statement:
--   The Local Ring Basic Facts construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsAlt.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsAlt.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalRingBasicFacts

theorem GlobalTheory.LocalRingBasicFacts.main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ}, Ideal.span (Set.range MvPowerSeries.X) ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by sorry
