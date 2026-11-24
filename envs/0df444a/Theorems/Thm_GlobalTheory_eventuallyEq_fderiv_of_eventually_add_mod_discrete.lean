-- Prove2me | Theorems.Thm_GlobalTheory_eventuallyEq_fderiv_of_eventually_add_mod_discrete
-- name    : GlobalTheory.eventuallyEq_fderiv_of_eventually_add_mod_discrete
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:04.131804+00:00
-- url     : https://prove2.me/theorems/1e09cca7-6d77-44d8-bf80-855f3bf26ffe
-- title:
--   Global Theory: eventually Eq fderiv of eventually add mod discrete
-- statement:
--   The Global Theory construction uses the eventually Eq fderiv of eventually add mod discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L57-L66

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

theorem GlobalTheory.eventuallyEq_fderiv_of_eventually_add_mod_discrete {Γ : AddSubgroup W}
    (hΓ : IsDiscrete (Γ : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : V × V in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    g =ᶠ[𝓝 0] fderiv 𝕜 g 0 := by sorry
