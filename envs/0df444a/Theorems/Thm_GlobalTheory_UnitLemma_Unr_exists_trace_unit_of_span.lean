-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_trace_unit_of_span
-- name    : GlobalTheory.UnitLemma.Unr.exists_trace_unit_of_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:48.06619+00:00
-- url     : https://prove2.me/theorems/1c0f4608-3b0e-436f-84d1-3179381545ab
-- title:
--   Unr: exists trace unit of span
-- statement:
--   The Unr construction uses the exists trace unit of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L93-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L93-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
open scoped nonZeroDivisors

theorem GlobalTheory.UnitLemma.Unr.exists_trace_unit_of_span (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by sorry
