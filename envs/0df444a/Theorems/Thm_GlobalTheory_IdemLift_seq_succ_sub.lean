-- Prove2me | Theorems.Thm_GlobalTheory_IdemLift_seq_succ_sub
-- name    : GlobalTheory.IdemLift.seq_succ_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:42.640153+00:00
-- url     : https://prove2.me/theorems/085cb49e-9e79-4aa2-92e1-2b75991cbf7e
-- title:
--   Idem Lift: seq succ sub
-- statement:
--   The Idem Lift construction uses the seq succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L58-L67

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

theorem GlobalTheory.IdemLift.seq_succ_sub (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x (k + 1) - seq x k) i j‖ ≤ ‖ϖ‖ ^ (2 ^ k) := by sorry
