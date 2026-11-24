-- Prove2me | Theorems.Thm_GlobalTheory_T_isSelfDual_pi_haar_traceStarDotProduct_unramified
-- name    : GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:07.440211+00:00
-- url     : https://prove2.me/theorems/a6928100-390b-44c7-9afe-a0eafb3be3c0
-- title:
--   T: is Self Dual pi haar trace Star Dot Product unramified
-- statement:
--   The T construction uses the is Self Dual pi haar trace Star Dot Product unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by sorry
