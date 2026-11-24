-- Prove2me | Theorems.Thm_GlobalTheory_exists_local_section_of_isDiscrete_ker
-- name    : GlobalTheory.exists_local_section_of_isDiscrete_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:11.453574+00:00
-- url     : https://prove2.me/theorems/ab2b5b8f-4933-45d5-89f2-3b63631539bc
-- title:
--   Global Theory: exists local section of is Discrete ker
-- statement:
--   The Global Theory construction uses the exists local section of is Discrete ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L148-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L148-L166

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

theorem GlobalTheory.exists_local_section_of_isDiscrete_ker {F : Type*} [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [TopologicalSpace A] {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0)) :
    ∃ s : A → F, s 0 = 0 ∧ ContinuousAt s 0 ∧ (∀ᶠ a in 𝓝 0, ex' (s a) = a) ∧
      ∀ᶠ z in 𝓝 0, s (ex' z) = z := by sorry
