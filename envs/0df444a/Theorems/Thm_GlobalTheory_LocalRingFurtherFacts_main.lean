-- Prove2me | Theorems.Thm_GlobalTheory_LocalRingFurtherFacts_main
-- name    : GlobalTheory.LocalRingFurtherFacts.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:31.013843+00:00
-- url     : https://prove2.me/theorems/65f7642e-3df5-4b41-95f1-dcc97c6e78c2
-- title:
--   Local Ring Further Facts: main
-- statement:
--   The Local Ring Further Facts construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsBis.lean#L4-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsBis.lean#L4-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalRingFurtherFacts

theorem GlobalTheory.LocalRingFurtherFacts.main {O : Type} [CommRing O] [IsLocalRing O] {a k : ℕ} {c : O}
    (hc : c ∈ IsLocalRing.maximalIdeal O ^ k) :
    (MvPowerSeries.C : O → MvPowerSeries (Fin a) O) c ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ k := by sorry
