-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_modCharacter_eq
-- name    : GroundTheory.Global.Cyclotomic.exists_modCharacter_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:47.332813+00:00
-- url     : https://prove2.me/theorems/19c09e09-29d2-42f5-bf76-b5247ac19457
-- title:
--   Cyclotomic: exists mod Character eq
-- statement:
--   The Cyclotomic construction uses the exists mod Character eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L151-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L151-L164

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
variable {n : ℕ} [NeZero n]

theorem GroundTheory.Global.Cyclotomic.exists_modCharacter_eq (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    ∃ σ : Gal(ℚ̄/ℚ), modCharacter n σ = a := by sorry
