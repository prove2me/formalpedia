-- Prove2me | Theorems.Thm_GlobalTheory_realLinear_eq_of_sub_mem_discrete
-- name    : GlobalTheory.realLinear_eq_of_sub_mem_discrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:04.936325+00:00
-- url     : https://prove2.me/theorems/2a3ade00-8c9c-40ce-a91f-8935c67242a9
-- title:
--   Global Theory: real Linear eq of sub mem discrete
-- statement:
--   The Global Theory construction uses the real Linear eq of sub mem discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L103-L113

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

theorem GlobalTheory.realLinear_eq_of_sub_mem_discrete {M : Type*} [AddCommGroup M] [Module ℝ M]
    {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {L L' : M →ₗ[ℝ] F}
    (h : ∀ x, L x - L' x ∈ Γ) : L = L' := by sorry
