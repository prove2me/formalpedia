-- Prove2me | Theorems.Thm_GlobalTheory_eventually_eq_zero_of_tendsto_of_mem_discrete
-- name    : GlobalTheory.eventually_eq_zero_of_tendsto_of_mem_discrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:31.921141+00:00
-- url     : https://prove2.me/theorems/871be9e0-84dd-4af4-9e63-b8a954327875
-- title:
--   Global Theory: eventually eq zero of tendsto of mem discrete
-- statement:
--   The Global Theory construction uses the eventually eq zero of tendsto of mem discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L12-L18

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.eventually_eq_zero_of_tendsto_of_mem_discrete {α F : Type*} [AddCommGroup F]
    [TopologicalSpace F] {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {l : Filter α}
    {f : α → F} (hf : Tendsto f l (𝓝 0)) (hm : ∀ᶠ a in l, f a ∈ Γ) : ∀ᶠ a in l, f a = 0 := by sorry
