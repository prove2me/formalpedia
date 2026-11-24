-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_mul
-- name    : GlobalTheory.Mem.GelfCheck.rowE_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:33.950749+00:00
-- url     : https://prove2.me/theorems/a0859256-e7f3-4b76-9468-fe236810d1e4
-- title:
--   Gelf Check: row E mul
-- statement:
--   The Gelf Check construction uses the row E mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean#L29-L36

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

theorem GlobalTheory.Mem.GelfCheck.rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P Q : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (P * Q) =
      _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P * Q + P * _root_.GlobalTheory.Mem.Gelf.rowE R r n a b Q := by sorry
