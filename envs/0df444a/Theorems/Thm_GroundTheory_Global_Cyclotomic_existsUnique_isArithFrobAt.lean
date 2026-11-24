-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_existsUnique_isArithFrobAt
-- name    : GroundTheory.Global.Cyclotomic.existsUnique_isArithFrobAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:35.45887+00:00
-- url     : https://prove2.me/theorems/7952cc89-5c1e-425c-947e-f956c6539909
-- title:
--   Cyclotomic: exists Unique is Arith Frob At
-- statement:
--   The Cyclotomic construction uses the exists Unique is Arith Frob At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L81-L87

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

theorem GroundTheory.Global.Cyclotomic.existsUnique_isArithFrobAt (hm : ¬ p ∣ m) : ∃! σ : Gal(K/ℚ), IsArithFrobAt ℤ σ P := by sorry
