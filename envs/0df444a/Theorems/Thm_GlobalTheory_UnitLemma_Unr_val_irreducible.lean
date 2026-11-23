-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_irreducible
-- name    : GlobalTheory.UnitLemma.Unr.val_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:19.847816+00:00
-- url     : https://prove2.me/theorems/56d2f2de-c4f8-459a-ae93-1c60a67a2539
-- title:
--   Unr: val irreducible
-- statement:
--   The Unr construction uses the val irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L46-L50

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

theorem GlobalTheory.UnitLemma.Unr.val_irreducible (K : UQ) {ϖ : K.O} (h : Irreducible ϖ) : val K.O (algebraMap K.O K.E ϖ) = 1 := by sorry
