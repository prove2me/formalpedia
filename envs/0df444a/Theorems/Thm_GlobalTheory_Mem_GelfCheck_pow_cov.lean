-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_pow_cov
-- name    : GlobalTheory.Mem.GelfCheck.pow_cov
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:07.787441+00:00
-- url     : https://prove2.me/theorems/c510e33b-8352-4af6-8c0e-34d2bb1ac970
-- title:
--   Gelf Check: pow cov
-- statement:
--   The Gelf Check construction uses the pow cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L133-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L133-L156

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
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}
open MvPolynomial
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}

theorem GlobalTheory.Mem.GelfCheck.pow_cov (h : _root_.GlobalTheory.Mem.Gelf.GlRel E) (k : ℕ)
    (a b c d : Fin N) :
    E c d * (E ^ k) a b - (E ^ k) a b * E c d =
      (if d = a then (E ^ k) c b else 0) - (if b = c then (E ^ k) a d else 0) := by sorry
