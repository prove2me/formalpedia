-- Prove2me | Theorems.Thm_GlobalTheory_CentralIdemIntegral_trace_leftMulMatrix
-- name    : GlobalTheory.CentralIdemIntegral.trace_leftMulMatrix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:42.561039+00:00
-- url     : https://prove2.me/theorems/a41ace0a-dece-4f67-8a44-a74bdb0fcbc4
-- title:
--   Central Idem Integral: trace left Mul Matrix
-- statement:
--   The Central Idem Integral construction uses the trace left Mul Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L54-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CentralIdemIntegral

theorem GlobalTheory.CentralIdemIntegral.trace_leftMulMatrix {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by sorry
