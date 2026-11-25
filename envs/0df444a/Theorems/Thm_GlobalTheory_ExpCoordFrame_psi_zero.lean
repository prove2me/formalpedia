-- Prove2me | Theorems.Thm_GlobalTheory_ExpCoordFrame_psi_zero
-- name    : GlobalTheory.ExpCoordFrame.psi_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:11.244147+00:00
-- url     : https://prove2.me/theorems/b09728ac-b14e-4757-a038-0fe7beaef456
-- title:
--   Exp Coord Frame: psi zero
-- statement:
--   The Exp Coord Frame construction uses the psi zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrame.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrame.lean#L35-L39

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
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {d : ℕ}
local notation "𝔢" => expPartialHomeomorph ℝ 𝔸

theorem GlobalTheory.ExpCoordFrame.psi_zero (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).source) : psi b x 0 = x := by sorry
