-- Prove2me | Theorems.Thm_GroundTheory_LocalField_continuous_localZeta_integrand
-- name    : GroundTheory.LocalField.continuous_localZeta_integrand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:23.821674+00:00
-- url     : https://prove2.me/theorems/95933145-2f58-5834-959b-b11da3ef54ac
-- title:
--   Local Field: continuous local Zeta integrand
-- statement:
--   The Local Field construction uses the continuous local Zeta integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L158-L163

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
omit [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.continuous_localZeta_integrand (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by sorry
