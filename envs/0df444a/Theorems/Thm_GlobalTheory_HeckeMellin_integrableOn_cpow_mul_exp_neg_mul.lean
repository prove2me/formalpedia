-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellin_integrableOn_cpow_mul_exp_neg_mul
-- name    : GlobalTheory.HeckeMellin.integrableOn_cpow_mul_exp_neg_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:08:29.830809+00:00
-- url     : https://prove2.me/theorems/553cf195-2cc0-4831-b5dc-be66a7ad6e09
-- title:
--   Hecke Mellin: integrable On cpow mul exp neg mul
-- statement:
--   The Hecke Mellin construction uses the integrable On cpow mul exp neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLine.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLine.lean#L12-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
open Set

theorem GlobalTheory.HeckeMellin.integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by sorry
