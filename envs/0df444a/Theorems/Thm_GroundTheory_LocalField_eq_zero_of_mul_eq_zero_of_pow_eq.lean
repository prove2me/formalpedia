-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_mul_eq_zero_of_pow_eq
-- name    : GroundTheory.LocalField.eq_zero_of_mul_eq_zero_of_pow_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:31.350983+00:00
-- url     : https://prove2.me/theorems/73ea7458-317f-5e4b-b9b2-a822102bfaa6
-- title:
--   Local Field: eq zero of mul eq zero of pow eq
-- statement:
--   The Local Field construction uses the eq zero of mul eq zero of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L163-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L163-L169

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
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
open PowerSeries
variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem GroundTheory.LocalField.eq_zero_of_mul_eq_zero_of_pow_eq (hP : P.Monic) {b : B}
    (hb : ∀ c : B, b * c = 0 → c = 0) {y : AdjoinRoot P} {k : ℕ} (hk : k ≠ 0)
    (hy : y ^ k = AdjoinRoot.of P b) {z : AdjoinRoot P} (h : y * z = 0) : z = 0 := by sorry
