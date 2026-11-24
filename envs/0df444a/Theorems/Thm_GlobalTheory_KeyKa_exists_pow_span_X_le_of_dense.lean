-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_pow_span_X_le_of_dense
-- name    : GlobalTheory.KeyKa.exists_pow_span_X_le_of_dense
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:08.783375+00:00
-- url     : https://prove2.me/theorems/bb992678-5f7f-40d4-82d1-cf663d559169
-- title:
--   Key Ka: exists pow span X le of dense
-- statement:
--   The Key Ka construction uses the exists pow span X le of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPowSpanXLeOfDense.lean#L7-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPowSpanXLeOfDense.lean#L7-L48

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

theorem GlobalTheory.KeyKa.exists_pow_span_X_le_of_dense (K : Type) [Field K] (g N : ℕ)
    (I : Ideal (MvPowerSeries (Fin g) K)) (ρ : Fin N → MvPowerSeries (Fin g) K)
    (h : ∀ (r : ℕ) (G : MvPowerSeries (Fin g) K), ∃ v : Fin N → K,
      G - ∑ k, v k • ρ k ∈ I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) :
    ∃ r : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I := by sorry
