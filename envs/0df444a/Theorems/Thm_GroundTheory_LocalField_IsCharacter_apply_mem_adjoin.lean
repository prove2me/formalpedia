-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin
-- name    : GroundTheory.LocalField.IsCharacter.apply_mem_adjoin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:31.697247+00:00
-- url     : https://prove2.me/theorems/500d6234-a905-4b91-ae15-11f74c9b8c82
-- title:
--   Is Character: apply mem adjoin
-- statement:
--   The Is Character construction uses the apply mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L84-L100

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.IsCharacter.apply_mem_adjoin {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {N : ℕ} [NeZero N]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : orderOf s ∣ N) :
    χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by sorry
