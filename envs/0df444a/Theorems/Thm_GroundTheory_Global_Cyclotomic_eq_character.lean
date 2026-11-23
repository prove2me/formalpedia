-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_character
-- name    : GroundTheory.Global.Cyclotomic.eq_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:38.164825+00:00
-- url     : https://prove2.me/theorems/c6eb6be9-80b4-4c53-ad48-2322478a6e92
-- title:
--   Cyclotomic: eq character
-- statement:
--   The Cyclotomic construction uses the eq character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L192-L196

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

theorem GroundTheory.Global.Cyclotomic.eq_character (σ : Gal(ℚ̄/ℚ)) (u : ℤ̂)
    (hu : ∀ (n : ℕ+) (t : ℚ̄), t ^ (n : ℕ) = 1 → σ t = t ^ (ProfiniteInteger.proj n u).val) :
    u = character σ := by sorry
