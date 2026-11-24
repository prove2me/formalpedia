-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_exists_pow_mul_eq_zero
-- name    : GlobalTheory.AffineThickening.exists_pow_mul_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:18.220244+00:00
-- url     : https://prove2.me/theorems/adde46b6-9f62-40d2-9fec-4ff38a722f19
-- title:
--   Affine Thickening: exists pow mul eq zero
-- statement:
--   The Affine Thickening construction uses the exists pow mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening

theorem GlobalTheory.AffineThickening.exists_pow_mul_eq_zero {Y : Scheme.{u}} {U V : Y.Opens} (hU : IsAffineOpen U)
    (h : V ≤ U) (g a : Γ(Y, U)) (e : V = Y.basicOpen g) (ha : rs h a = 0) :
    ∃ n : ℕ, g ^ n * a = 0 := by sorry
