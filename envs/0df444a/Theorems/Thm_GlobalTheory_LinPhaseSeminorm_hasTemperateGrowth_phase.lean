-- Prove2me | Theorems.Thm_GlobalTheory_LinPhaseSeminorm_hasTemperateGrowth_phase
-- name    : GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:08.720614+00:00
-- url     : https://prove2.me/theorems/2bd6eb81-d8a1-468b-8fd6-a7de431a9820
-- title:
--   Lin Phase Seminorm: has Temperate Growth phase
-- statement:
--   The Lin Phase Seminorm construction uses the has Temperate Growth phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L68-L76

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

theorem GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c t : ℝ) : Function.HasTemperateGrowth (phaseLine c t ∘ ⇑L) := by sorry
