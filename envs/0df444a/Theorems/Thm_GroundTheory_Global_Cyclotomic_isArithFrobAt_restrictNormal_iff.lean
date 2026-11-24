-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isArithFrobAt_restrictNormal_iff
-- name    : GroundTheory.Global.Cyclotomic.isArithFrobAt_restrictNormal_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:48.300911+00:00
-- url     : https://prove2.me/theorems/f5cc5d8a-01ec-498f-aae5-ace77fbe5229
-- title:
--   Cyclotomic: is Arith Frob At restrict Normal iff
-- statement:
--   The Cyclotomic construction uses the is Arith Frob At restrict Normal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L268-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L268-L287

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
variable (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (rootsOfUnityField m)))
  [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

theorem GroundTheory.Global.Cyclotomic.isArithFrobAt_restrictNormal_iff (hm : ¬ p ∣ m) (σ : Gal(ℚ̄/ℚ)) :
    IsArithFrobAt ℤ (σ.restrictNormal (rootsOfUnityField m)) P ↔
      (modCharacter m σ : ZMod m) = p := by sorry
