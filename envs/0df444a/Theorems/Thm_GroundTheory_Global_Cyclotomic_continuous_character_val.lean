-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_character_val
-- name    : GroundTheory.Global.Cyclotomic.continuous_character_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:36.722276+00:00
-- url     : https://prove2.me/theorems/31f40a4a-9faa-4d43-8c0f-771ab2f346dc
-- title:
--   Cyclotomic: continuous character val
-- statement:
--   The Cyclotomic construction uses the continuous character val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L198-L200

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.continuous_character_val : Continuous fun σ : Gal(ℚ̄/ℚ) => (character σ : ℤ̂) := by sorry
