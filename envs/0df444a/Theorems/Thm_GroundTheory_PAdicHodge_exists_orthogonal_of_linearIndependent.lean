-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_of_linearIndependent
-- name    : GroundTheory.PAdicHodge.exists_orthogonal_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:44.215017+00:00
-- url     : https://prove2.me/theorems/25bbb9bf-cc99-4c4f-8b0a-3bfaba4e708a
-- title:
--   PAdic Hodge: exists orthogonal of linear Independent
-- statement:
--   The PAdic Hodge construction uses the exists orthogonal of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L130-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L130-L161

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
variable [CompleteSpace k]

theorem GroundTheory.PAdicHodge.exists_orthogonal_of_linearIndependent {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent k v) {t : ℝ} (ht : t < 1) :
    ∃ w : ι → E, LinearIndependent k w ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : ι → k) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by sorry
