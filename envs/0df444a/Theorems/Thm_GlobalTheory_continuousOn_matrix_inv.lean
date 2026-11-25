-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_matrix_inv
-- name    : GlobalTheory.continuousOn_matrix_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:37.133457+00:00
-- url     : https://prove2.me/theorems/6e86a95a-6675-4f53-a83d-68912941f13e
-- title:
--   Global Theory: continuous On matrix inv
-- statement:
--   The Global Theory construction uses the continuous On matrix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L729-L734
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L729-L734

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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]

theorem GlobalTheory.continuousOn_matrix_inv {A : X → Matrix n n ℂ} (hA : ContinuousOn A U)
    (hu : ∀ x ∈ U, IsUnit (A x)) : ContinuousOn (fun x => (A x)⁻¹) U := by sorry
