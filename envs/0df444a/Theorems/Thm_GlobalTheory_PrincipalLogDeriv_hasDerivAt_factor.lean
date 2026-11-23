-- Prove2me | Theorems.Thm_GlobalTheory_PrincipalLogDeriv_hasDerivAt_factor
-- name    : GlobalTheory.PrincipalLogDeriv.hasDerivAt_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:43.942806+00:00
-- url     : https://prove2.me/theorems/5d4f0262-f97b-4f20-ae3d-949233759f29
-- title:
--   Principal Log Deriv: has Deriv At factor
-- statement:
--   The Principal Log Deriv construction uses the has Deriv At factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NegReLogDerivPrincipalLFunctionLe.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NegReLogDerivPrincipalLFunctionLe.lean#L31-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PrincipalLogDeriv

theorem GlobalTheory.PrincipalLogDeriv.hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by sorry
