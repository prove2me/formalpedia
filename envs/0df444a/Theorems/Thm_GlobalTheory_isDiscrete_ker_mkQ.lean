-- Prove2me | Theorems.Thm_GlobalTheory_isDiscrete_ker_mkQ
-- name    : GlobalTheory.isDiscrete_ker_mkQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:22.788829+00:00
-- url     : https://prove2.me/theorems/3562dceb-b31b-4d0c-9f75-4dd9e08e4bb3
-- title:
--   Global Theory: is Discrete ker mk Q
-- statement:
--   The Global Theory construction uses the is Discrete ker mk Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L357-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L357-L363

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
  [NormedSpace ℝ F]

theorem GlobalTheory.isDiscrete_ker_mkQ {M : Type*} [AddCommGroup M] [TopologicalSpace M] (Λ : Submodule ℤ M)
    [DiscreteTopology Λ] : IsDiscrete (Λ.mkQ.toAddMonoidHom.ker : Set M) := by sorry
