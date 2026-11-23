-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
-- name    : GroundTheory.LocalField.IsCharacter.isClassFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:24.218279+00:00
-- url     : https://prove2.me/theorems/7c71ff3c-16f4-478c-a5d2-05b5b5c232b0
-- title:
--   Is Character: is Class Fun
-- statement:
--   The Is Character construction uses the is Class Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L358-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L358-L361

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
variable {G : Type*} [Group G] [Fintype G]
omit [Fintype G]

theorem GroundTheory.LocalField.IsCharacter.isClassFun {χ : G → ℂ} (h : IsCharacter χ) : IsClassFun χ := by sorry
