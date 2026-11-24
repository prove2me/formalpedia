-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_germ
-- name    : GlobalTheory.existsUnique_linear_lift_of_germ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:18.618806+00:00
-- url     : https://prove2.me/theorems/1c885373-7557-44ad-ac6a-ffce6e5c5a97
-- title:
--   Global Theory: exists Unique linear lift of germ
-- statement:
--   The Global Theory construction uses the exists Unique linear lift of germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L198-L205

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

theorem GlobalTheory.existsUnique_linear_lift_of_germ {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {g : V → W} (hd : DifferentiableAt 𝕜 g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V →L[𝕜] W, ∀ z, ex' (L z) = ex z := by sorry
