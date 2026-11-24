-- Prove2me | Theorems.Thm_GlobalTheory_Div_LipschitzCone_sign_cone_iff
-- name    : GlobalTheory.Div.LipschitzCone.sign_cone_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:04.539981+00:00
-- url     : https://prove2.me/theorems/1eb96bae-75d3-416a-a9ac-2845ac817d03
-- title:
--   Lipschitz Cone: sign cone iff
-- statement:
--   The Lipschitz Cone construction uses the sign cone iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemTraceDualSignedPositiveConeIffTotallyPositive.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemTraceDualSignedPositiveConeIffTotallyPositive.lean#L10-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.LipschitzCone

theorem GlobalTheory.Div.LipschitzCone.sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by sorry
