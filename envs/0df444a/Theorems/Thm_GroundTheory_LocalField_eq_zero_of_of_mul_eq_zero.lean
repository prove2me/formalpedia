-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_of_mul_eq_zero
-- name    : GroundTheory.LocalField.eq_zero_of_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:58.3568+00:00
-- url     : https://prove2.me/theorems/e2f96831-276d-4fb7-b1fa-1fd4651ff855
-- title:
--   Local Field: eq zero of of mul eq zero
-- statement:
--   The Local Field construction uses the eq zero of of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L150-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L150-L161

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

theorem GroundTheory.LocalField.eq_zero_of_of_mul_eq_zero (hP : P.Monic) {b : B} (hb : ∀ c : B, b * c = 0 → c = 0)
    {z : AdjoinRoot P} (h : AdjoinRoot.of P b * z = 0) : z = 0 := by sorry
