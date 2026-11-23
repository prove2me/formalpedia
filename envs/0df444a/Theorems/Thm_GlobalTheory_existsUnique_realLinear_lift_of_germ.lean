-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_realLinear_lift_of_germ
-- name    : GlobalTheory.existsUnique_realLinear_lift_of_germ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:09.333374+00:00
-- url     : https://prove2.me/theorems/1fac0303-14f0-4d90-9e5e-fde7443b4de2
-- title:
--   Global Theory: exists Unique real Linear lift of germ
-- statement:
--   The Global Theory construction uses the exists Unique real Linear lift of germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L127-L146

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

theorem GlobalTheory.existsUnique_realLinear_lift_of_germ {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by sorry
