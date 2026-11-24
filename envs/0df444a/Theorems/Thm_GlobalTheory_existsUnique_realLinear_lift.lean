-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_realLinear_lift
-- name    : GlobalTheory.existsUnique_realLinear_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:34.291118+00:00
-- url     : https://prove2.me/theorems/94a90f12-cb67-4cf9-8570-3c6041433bf8
-- title:
--   Global Theory: exists Unique real Linear lift
-- statement:
--   The Global Theory construction uses the exists Unique real Linear lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L168-L174

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

theorem GlobalTheory.existsUnique_realLinear_lift [TopologicalSpace A] {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0))
    (hc : ContinuousAt ex 0) : ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by sorry
