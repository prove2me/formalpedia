-- Prove2me | Theorems.Thm_GlobalTheory_IdemLift_seq_inv
-- name    : GlobalTheory.IdemLift.seq_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:41.936686+00:00
-- url     : https://prove2.me/theorems/5cca5693-9aec-4cd0-9846-e943c0931ff2
-- title:
--   Idem Lift: seq inv
-- statement:
--   The Idem Lift construction uses the seq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L40-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.IdemLift.seq_inv (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    (∀ i j, ‖seq x k i j‖ ≤ 1) ∧ seq x k * N = N * seq x k ∧
      ∃ b : Matrix (Fin n) (Fin n) E, (∀ i j, ‖b i j‖ ≤ 1) ∧
        seq x k * seq x k - seq x k = ϖ ^ (2 ^ k) • b := by sorry
