-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLocal_order_shift
-- name    : GlobalTheory.ZetaLocal.order_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:42.859824+00:00
-- url     : https://prove2.me/theorems/f820b218-b7d8-494a-a59f-b5b823549070
-- title:
--   Zeta Local: order shift
-- statement:
--   The Zeta Local construction uses the order shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L28-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal

theorem GlobalTheory.ZetaLocal.order_shift (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by sorry
