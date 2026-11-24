-- Prove2me | Theorems.Thm_GlobalTheory_StdChar_locConst
-- name    : GlobalTheory.StdChar.locConst
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:51.99614+00:00
-- url     : https://prove2.me/theorems/982b82bb-29f2-4ccd-a2f4-2d78da5317c5
-- title:
--   Std Char: loc Const
-- statement:
--   The Std Char construction uses the loc Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorProperties.lean#L122-L129

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

theorem GlobalTheory.StdChar.locConst [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by sorry
