-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_mul
-- name    : GroundTheory.LocalField.IsCharacter.mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:58.315335+00:00
-- url     : https://prove2.me/theorems/af3d11e9-8f23-4abe-8126-807b4f176bde
-- title:
--   Is Character: mul
-- statement:
--   The Is Character construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L464-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L464-L468

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
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
variable {G : Type*} [Group G]

theorem GroundTheory.LocalField.IsCharacter.mul {χ ψ : G → ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    IsCharacter (χ * ψ) := by sorry
