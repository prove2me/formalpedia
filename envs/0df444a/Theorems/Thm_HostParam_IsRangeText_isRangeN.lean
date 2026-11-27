-- Prove2me | Theorems.Thm_HostParam_IsRangeText_isRangeN
-- name    : HostParam.IsRangeText.isRangeN
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:44.265901+00:00
-- url     : https://prove2.me/theorems/5eb9f73a-687d-4c22-bb68-6e7cbc684e80
-- title:
--   Is Range Text: is Range N
-- statement:
--   The Is Range Text construction uses the is Range N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/QuadraticCharacters/PreHostA.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/QuadraticCharacters/PreHostA.lean#L78-L88

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_LogDerivAtOne
import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_PreHostA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
open HostParam

theorem HostParam.IsRangeText.isRangeN {T : HostType} {x : ℝ} {e : ℕ} (h : IsRangeText T x e) (hx : 3 ≤ x) :
    IsRangeN T x e := by sorry
