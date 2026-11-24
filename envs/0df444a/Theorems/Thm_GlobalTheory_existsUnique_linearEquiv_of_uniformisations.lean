-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_linearEquiv_of_uniformisations
-- name    : GlobalTheory.existsUnique_linearEquiv_of_uniformisations
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:13.326129+00:00
-- url     : https://prove2.me/theorems/4281704c-c529-4332-8179-0da057cdab91
-- title:
--   Global Theory: exists Unique linear Equiv of uniformisations
-- statement:
--   The Global Theory construction uses the exists Unique linear Equiv of uniformisations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L238-L244

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

theorem GlobalTheory.existsUnique_linearEquiv_of_uniformisations [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] {ex : V →+ A} {ex' : W →+ A} (hk : IsDiscrete (ex.ker : Set V))
    (hk' : IsDiscrete (ex'.ker : Set W)) (hr : ex'.range ≤ ex.range) {g : V → W}
    (hd : DifferentiableAt 𝕜 g 0) (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : V ≃L[𝕜] W, (∀ z, ex' (L z) = ex z) ∧ ex.ker.map (L : V →+ W) = ex'.ker := by sorry
