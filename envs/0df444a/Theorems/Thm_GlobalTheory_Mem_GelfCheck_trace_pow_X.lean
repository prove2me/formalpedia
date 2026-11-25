-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_trace_pow_X
-- name    : GlobalTheory.Mem.GelfCheck.trace_pow_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:06.742668+00:00
-- url     : https://prove2.me/theorems/2647dcad-001c-5a8d-be1a-06fcafae05b7
-- title:
--   Gelf Check: trace pow X
-- statement:
--   The Gelf Check construction uses the trace pow X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L298-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L298-L302

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

theorem GlobalTheory.Mem.GelfCheck.trace_pow_X (R : Type) [CommRing R] (r n : ℕ) (t : Fin n) (k : ℕ) :
    (rowE R (r+1) n ^ k).trace (X (0, t)) = gelfC (Pi.single (0 : Fin (r+1)) (1 : R)) k • X (0, t) := by sorry
