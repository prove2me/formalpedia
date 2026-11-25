-- Prove2me | Theorems.Thm_GlobalTheory_isLogBoundedScalar_iff_abs_log_le
-- name    : GlobalTheory.isLogBoundedScalar_iff_abs_log_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:15.28063+00:00
-- url     : https://prove2.me/theorems/59f46558-8e7d-4b69-87b3-3d240bab43a0
-- title:
--   Global Theory: is Log Bounded Scalar iff abs log le
-- statement:
--   The Global Theory construction uses the is Log Bounded Scalar iff abs log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L267-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L267-L286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}

theorem GlobalTheory.isLogBoundedScalar_iff_abs_log_le : IsLogBoundedScalar S w U g ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x) ∧ ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ),
      ∀ x ∈ K, x ∉ coordDivisor S w →
        |Real.log (g x)| ≤ C + N * Real.log (lwP₂ S (w x)) := by sorry
