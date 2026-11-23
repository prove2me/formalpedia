-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_pow_val_one
-- name    : GroundTheory.Global.Cyclotomic.pow_val_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:51.704046+00:00
-- url     : https://prove2.me/theorems/79ea1ad7-21c6-407c-941c-c851aa9ff957
-- title:
--   Cyclotomic: pow val one
-- statement:
--   The Cyclotomic construction uses the pow val one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L80-L83

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

theorem GroundTheory.Global.Cyclotomic.pow_val_one {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) :
    t ^ (1 : ZMod n).val = t := by sorry
