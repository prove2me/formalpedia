-- Prove2me | Theorems.Thm_GlobalTheory_StdChar_mem_intSub
-- name    : GlobalTheory.StdChar.mem_intSub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:09.256409+00:00
-- url     : https://prove2.me/theorems/8e190458-b0e1-4fbc-bb97-36079f273662
-- title:
--   Std Char: mem int Sub
-- statement:
--   The Std Char construction uses the mem int Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L68-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L68-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]

theorem GlobalTheory.StdChar.mem_intSub [IsUltrametricDist F] {x : F} : x ∈ intSub F ↔ ‖x‖ ≤ 1 := by sorry
