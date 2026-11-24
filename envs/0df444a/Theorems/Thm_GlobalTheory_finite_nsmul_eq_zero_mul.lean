-- Prove2me | Theorems.Thm_GlobalTheory_finite_nsmul_eq_zero_mul
-- name    : GlobalTheory.finite_nsmul_eq_zero_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:54.650363+00:00
-- url     : https://prove2.me/theorems/66eee742-9e74-45bb-8181-e6ba4d686b5e
-- title:
--   Global Theory: finite nsmul eq zero mul
-- statement:
--   The Global Theory construction uses the finite nsmul eq zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L48-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem GlobalTheory.finite_nsmul_eq_zero_mul {G : Type*} [AddCommGroup G] {m n : ℕ}
    (hm : {x : G | m • x = 0}.Finite) (hn : {x : G | n • x = 0}.Finite) :
    {x : G | (m * n) • x = 0}.Finite := by sorry
