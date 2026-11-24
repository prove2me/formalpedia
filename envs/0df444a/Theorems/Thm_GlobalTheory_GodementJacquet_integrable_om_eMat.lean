-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_integrable_om_eMat
-- name    : GlobalTheory.GodementJacquet.integrable_om_eMat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:09.812854+00:00
-- url     : https://prove2.me/theorems/d9da81f7-b826-478c-9c47-6e2cda84a0f9
-- title:
--   Godement Jacquet: integrable om e Mat
-- statement:
--   The Godement Jacquet construction uses the integrable om e Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrable.lean#L37-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrable.lean#L37-L115

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

theorem GlobalTheory.GodementJacquet.integrable_om_eMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by sorry
