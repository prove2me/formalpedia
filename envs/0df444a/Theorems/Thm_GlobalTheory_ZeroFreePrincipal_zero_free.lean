-- Prove2me | Theorems.Thm_GlobalTheory_ZeroFreePrincipal_zero_free
-- name    : GlobalTheory.ZeroFreePrincipal.zero_free
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:49.887813+00:00
-- url     : https://prove2.me/theorems/0fb8e7e8-f810-4d11-8867-be5cf9996f78
-- title:
--   Zero Free Principal: zero free
-- statement:
--   The Zero Free Principal construction uses the zero free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZeroFreePrincipal.lean#L281-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZeroFreePrincipal.lean#L281-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZeroFreePrincipal
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

theorem GlobalTheory.ZeroFreePrincipal.zero_free : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
    s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
    s.re < 1 - c / Real.log (q * (|s.im| + 2)) := by sorry
