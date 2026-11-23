-- Prove2me | Theorems.Thm_GlobalTheory_LinPhaseSeminorm_contDiff_phaseLine
-- name    : GlobalTheory.LinPhaseSeminorm.contDiff_phaseLine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:51.113087+00:00
-- url     : https://prove2.me/theorems/a3deb84c-3c1d-481f-ba12-a398241b1864
-- title:
--   Lin Phase Seminorm: cont Diff phase Line
-- statement:
--   The Lin Phase Seminorm construction uses the cont Diff phase Line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm

theorem GlobalTheory.LinPhaseSeminorm.contDiff_phaseLine (c t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phaseLine c t) := by sorry
