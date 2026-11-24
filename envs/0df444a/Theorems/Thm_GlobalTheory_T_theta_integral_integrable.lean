-- Prove2me | Theorems.Thm_GlobalTheory_T_theta_integral_integrable
-- name    : GlobalTheory.T.theta_integral_integrable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:50.324142+00:00
-- url     : https://prove2.me/theorems/c1b3daf6-0024-4f8f-aa71-3f1201d13b66
-- title:
--   T: theta integral integrable
-- statement:
--   The T construction uses the theta integral integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrableStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaIntegralIntegrableStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.theta_integral_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by sorry
