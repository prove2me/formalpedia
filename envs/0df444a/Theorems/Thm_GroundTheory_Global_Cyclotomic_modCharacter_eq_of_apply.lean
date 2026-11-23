-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_apply
-- name    : GroundTheory.Global.Cyclotomic.modCharacter_eq_of_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:11.876288+00:00
-- url     : https://prove2.me/theorems/c8aea2b6-ee72-488a-9c3f-a592913b5b59
-- title:
--   Cyclotomic: mod Character eq of apply
-- statement:
--   The Cyclotomic construction uses the mod Character eq of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L113-L117

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

theorem GroundTheory.Global.Cyclotomic.modCharacter_eq_of_apply {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)}
    {c : ZMod n} (h : σ ζ = ζ ^ c.val) : (modCharacter n σ : ZMod n) = c := by sorry
