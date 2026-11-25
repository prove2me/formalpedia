-- Prove2me | Theorems.Thm_GlobalTheory_SobolevRep_integrable_integral_cons
-- name    : GlobalTheory.SobolevRep.integrable_integral_cons
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:38.291231+00:00
-- url     : https://prove2.me/theorems/93d79cdc-b4e2-47b5-8d7b-1cbdac9b5f3c
-- title:
--   Sobolev Rep: integrable integral cons
-- statement:
--   The Sobolev Rep construction uses the integrable integral cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExp.lean#L57-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExp.lean#L57-L77

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
open GlobalTheory.SobolevRep
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem GlobalTheory.SobolevRep.integrable_integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t'))) := by sorry
