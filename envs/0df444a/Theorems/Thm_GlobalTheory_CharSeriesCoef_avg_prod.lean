-- Prove2me | Theorems.Thm_GlobalTheory_CharSeriesCoef_avg_prod
-- name    : GlobalTheory.CharSeriesCoef.avg_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:05.176876+00:00
-- url     : https://prove2.me/theorems/122ccdb0-db0e-48ea-8222-6293a242b34d
-- title:
--   Char Series Coef: avg prod
-- statement:
--   The Char Series Coef construction uses the avg prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L21-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef

theorem GlobalTheory.CharSeriesCoef.avg_prod {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by sorry
