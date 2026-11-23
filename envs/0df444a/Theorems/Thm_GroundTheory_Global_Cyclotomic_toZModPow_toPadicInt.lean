-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_toZModPow_toPadicInt
-- name    : GroundTheory.Global.Cyclotomic.toZModPow_toPadicInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:05.4088+00:00
-- url     : https://prove2.me/theorems/6b66bf95-39b7-4749-8976-d9460a9136d9
-- title:
--   Cyclotomic: to ZMod Pow to Padic Int
-- statement:
--   The Cyclotomic construction uses the to ZMod Pow to Padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L306-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L306-L309

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
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Global.Cyclotomic.toZModPow_toPadicInt (k : ℕ) (x : ℤ̂) :
    PadicInt.toZModPow k (toPadicInt ℓ x) =
      ProfiniteInteger.proj (primePowPNat ℓ k) x := by sorry
