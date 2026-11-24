-- Prove2me | Theorems.Thm_GlobalTheory_eventually_eq_lift_add
-- name    : GlobalTheory.eventually_eq_lift_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:00.097191+00:00
-- url     : https://prove2.me/theorems/5d227529-f9af-4ebe-877a-d72b909df16e
-- title:
--   Global Theory: eventually eq lift add
-- statement:
--   The Global Theory construction uses the eventually eq lift add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L115-L125

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]

theorem GlobalTheory.eventually_eq_lift_add {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : E →L[ℝ] F} (hL : ∀ z, ex' (L z) = ex z) :
    ∀ᶠ z in 𝓝 0, g z = L z + g 0 := by sorry
