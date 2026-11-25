-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_IsArithFrobAt_apply_of_pow_eq_one
-- name    : GroundTheory.Global.Cyclotomic.IsArithFrobAt.apply_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:32.475581+00:00
-- url     : https://prove2.me/theorems/f2be538b-78db-4cc0-bc6a-03c00b41470b
-- title:
--   Is Arith Frob At: apply of pow eq one
-- statement:
--   The Is Arith Frob At construction uses the apply of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L57-L69

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
omit hp [IsCyclotomicExtension {m} ℚ K] [P.IsPrime]

theorem GroundTheory.Global.Cyclotomic.IsArithFrobAt.apply_of_pow_eq_one (hm : ¬ p ∣ m) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) {x : K} (hx : x ^ m = 1) : σ x = x ^ p := by sorry
