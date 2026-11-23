-- Prove2me | Theorems.Thm_GlobalTheory_realLinear_eq_fderiv_of_eventuallyEq
-- name    : GlobalTheory.realLinear_eq_fderiv_of_eventuallyEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:46.028855+00:00
-- url     : https://prove2.me/theorems/69cea0ae-5069-4031-96a0-46318d1c3a15
-- title:
--   Global Theory: real Linear eq fderiv of eventually Eq
-- statement:
--   The Global Theory construction uses the real Linear eq fderiv of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L51-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]

theorem GlobalTheory.realLinear_eq_fderiv_of_eventuallyEq {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    {L : V →L[ℝ] W} {c : W} (hL : ∀ᶠ z in 𝓝 0, g z = L z + c) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ := by sorry
