-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_sub_mem_of_dense
-- name    : GlobalTheory.KeyKa.exists_sub_mem_of_dense
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:21.904806+00:00
-- url     : https://prove2.me/theorems/624dde1d-9d03-4606-86c1-dbfe350da02f
-- title:
--   Key Ka: exists sub mem of dense
-- statement:
--   The Key Ka construction uses the exists sub mem of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPowSpanXLeOfDense.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPowSpanXLeOfDense.lean#L50-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPowSpanXLeOfDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.exists_sub_mem_of_dense : ∀ (K : Type) [Field K] (g N : ℕ) (Y : Type) [Finite Y] (I : Y → Ideal (MvPowerSeries (Fin g) K)) (ρ : Y → Fin N → MvPowerSeries (Fin g) K), (∀ (r : ℕ) (G : Y → MvPowerSeries (Fin g) K), ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) → ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y := by sorry
