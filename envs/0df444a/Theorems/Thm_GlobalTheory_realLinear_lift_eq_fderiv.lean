-- Prove2me | Theorems.Thm_GlobalTheory_realLinear_lift_eq_fderiv
-- name    : GlobalTheory.realLinear_lift_eq_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:43.062093+00:00
-- url     : https://prove2.me/theorems/e05ed1b3-6b4b-4506-ab79-4e13e5f08ce8
-- title:
--   Global Theory: real Linear lift eq fderiv
-- statement:
--   The Global Theory construction uses the real Linear lift eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L185-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L185-L189

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
  {A : Type*} [AddCommGroup A]

theorem GlobalTheory.realLinear_lift_eq_fderiv {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : V →L[ℝ] W} (hL : ∀ z, ex' (L z) = ex z) :
    L = (fderiv 𝕜 g 0).restrictScalars ℝ := by sorry
