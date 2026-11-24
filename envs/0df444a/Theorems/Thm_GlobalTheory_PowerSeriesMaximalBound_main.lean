-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_main
-- name    : GlobalTheory.PowerSeriesMaximalBound.main
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:41.494726+00:00
-- url     : https://prove2.me/theorems/79e598be-9768-49cb-bb31-bbb8345e8c12
-- title:
--   Power Series Maximal Bound: main
-- statement:
--   The Power Series Maximal Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L32-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem GlobalTheory.PowerSeriesMaximalBound.main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a N : ℕ} (v : Fin a →₀ ℕ) {c : O}, c ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) v) → (MvPowerSeries.monomial v : O → MvPowerSeries (Fin a) O) c ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by sorry
