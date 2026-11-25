-- Prove2me | Theorems.Thm_GlobalTheory_ExpCoordFrame_differentiableAt_psi
-- name    : GlobalTheory.ExpCoordFrame.differentiableAt_psi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:22.923187+00:00
-- url     : https://prove2.me/theorems/7f78c55e-6925-48de-baef-48f549445f3d
-- title:
--   Exp Coord Frame: differentiable At psi
-- statement:
--   The Exp Coord Frame construction uses the differentiable At psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrame.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrame.lean#L75-L80

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpCoordFrame
open NormedSpace Filter Topology

theorem GlobalTheory.ExpCoordFrame.differentiableAt_psi {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {𝔤 : Submodule ℝ 𝔸} {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (expPartialHomeomorph ℝ 𝔸).source) :
    DifferentiableAt ℝ (psi b x) 0 := by sorry
