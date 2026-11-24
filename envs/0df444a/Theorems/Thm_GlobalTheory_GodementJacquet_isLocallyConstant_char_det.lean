-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_isLocallyConstant_char_det
-- name    : GlobalTheory.GodementJacquet.isLocallyConstant_char_det
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:14.340796+00:00
-- url     : https://prove2.me/theorems/f75d7fc6-ee91-4ad5-b4ff-c05174b7e7ea
-- title:
--   Godement Jacquet: is Locally Constant char det
-- statement:
--   The Godement Jacquet construction uses the is Locally Constant char det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrable.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrable.lean#L21-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.GodementJacquet.isLocallyConstant_char_det {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by sorry
