-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_un_val
-- name    : GlobalTheory.OppRad.un_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:48.843537+00:00
-- url     : https://prove2.me/theorems/eaa703d5-3231-42f3-80d8-497e12cdbdc7
-- title:
--   Opp Rad: un val
-- statement:
--   The Opp Rad construction uses the un val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L36-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]

theorem GlobalTheory.OppRad.un_val (x : R) (h : x * x = 0) : (un x h).val = 1 + x := by sorry

attribute [defeq] GlobalTheory.OppRad.un_val
