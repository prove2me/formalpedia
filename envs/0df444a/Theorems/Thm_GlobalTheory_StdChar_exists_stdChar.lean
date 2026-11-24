-- Prove2me | Theorems.Thm_GlobalTheory_StdChar_exists_stdChar
-- name    : GlobalTheory.StdChar.exists_stdChar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:22:13.329064+00:00
-- url     : https://prove2.me/theorems/19fe008a-f15e-49c6-a71a-a26adde80a3d
-- title:
--   Std Char: exists std Char
-- statement:
--   The Std Char construction uses the exists std Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L102-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L102-L115

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
variable (F)

theorem GlobalTheory.StdChar.exists_stdChar [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by sorry
