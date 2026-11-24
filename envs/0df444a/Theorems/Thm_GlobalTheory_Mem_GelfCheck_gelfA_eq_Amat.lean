-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_gelfA_eq_Amat
-- name    : GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:10.093882+00:00
-- url     : https://prove2.me/theorems/83323480-5576-4c7b-8368-3a5dae2e898c
-- title:
--   Gelf Check: gelf A eq Amat
-- statement:
--   The Gelf Check construction uses the gelf A eq Amat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L115-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L115-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial

theorem GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat {N : ℕ} (μ : Fin N → ℂ) :
    _root_.GlobalTheory.Mem.Gelf.gelfA μ = _root_.Formalism.REAL.Amat (_root_.Formalism.REAL.lsh μ) := by sorry
