-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_det_notMem_span
-- name    : GlobalTheory.SocleDet.det_notMem_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:00.564447+00:00
-- url     : https://prove2.me/theorems/675f47ad-4d62-47bd-a961-807f5fd981e7
-- title:
--   Socle Det: det not Mem span
-- statement:
--   The Socle Det construction uses the det not Mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L170-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L170-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix

theorem GlobalTheory.SocleDet.det_notMem_span (k : Type) [Field k] (g N : ℕ) (f : Fin g → MvPowerSeries (Fin g) k)
    (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k))
    (hf : ∀ i, f i = ∑ j, a i j * MvPowerSeries.X j)
    (hN : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by sorry
