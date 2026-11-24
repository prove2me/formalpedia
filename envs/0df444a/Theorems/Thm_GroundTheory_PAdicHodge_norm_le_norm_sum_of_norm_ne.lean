-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_le_norm_sum_of_norm_ne
-- name    : GroundTheory.PAdicHodge.norm_le_norm_sum_of_norm_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:48.290267+00:00
-- url     : https://prove2.me/theorems/d7a3191e-14e4-479d-be7e-4ff58c45cedb
-- title:
--   PAdic Hodge: norm le norm sum of norm ne
-- statement:
--   The PAdic Hodge construction uses the norm le norm sum of norm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L16-L35

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
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
open IntermediateField Polynomial
variable {R : Type*} [NormedField R] [IsUltrametricDist R]

theorem GroundTheory.PAdicHodge.norm_le_norm_sum_of_norm_ne {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) :
    ∀ i ∈ s, ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by sorry
