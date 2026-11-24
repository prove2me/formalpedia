-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_eq_rowDiv
-- name    : GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:19.377363+00:00
-- url     : https://prove2.me/theorems/3081f1a5-82f3-456f-98c0-02b6bd320228
-- title:
--   Gelf Check: row E eq row Div
-- statement:
--   The Gelf Check construction uses the row E eq row Div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L104-L109

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

theorem GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 1 P ∧ _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 0 P = P := by sorry
