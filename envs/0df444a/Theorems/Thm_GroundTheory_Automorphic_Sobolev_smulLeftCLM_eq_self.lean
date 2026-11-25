-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_self
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:20.959607+00:00
-- url     : https://prove2.me/theorems/392ebd53-f9fe-419d-a132-6a2e0f1d4d70
-- title:
--   Sobolev: smul Left CLM eq self
-- statement:
--   The Sobolev construction uses the smul Left CLM eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L315-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L315-L329

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_self {g : E → ℂ} (hg : g.HasTemperateGrowth) {V U : Set E} (hV : IsOpen V)
    (hg1 : ∀ x ∈ V, g x = 1) (hVU : Vᶜ ⊆ U) {z : 𝓢'(E, ℂ)} (hz : Distribution.IsVanishingOn z U) :
    smulLeftCLM ℂ g z = z := by sorry
