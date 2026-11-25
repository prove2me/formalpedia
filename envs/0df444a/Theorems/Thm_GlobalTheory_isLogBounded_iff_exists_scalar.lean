-- Prove2me | Theorems.Thm_GlobalTheory_isLogBounded_iff_exists_scalar
-- name    : GlobalTheory.isLogBounded_iff_exists_scalar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:42.619474+00:00
-- url     : https://prove2.me/theorems/532aa877-e579-4ac0-92cd-93103488727c
-- title:
--   Global Theory: is Log Bounded iff exists scalar
-- statement:
--   The Global Theory construction uses the is Log Bounded iff exists scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L703-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L703-L727

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

theorem GlobalTheory.isLogBounded_iff_exists_scalar : IsLogBounded S w U G ↔
    ∃ g : X → ℝ, IsLogBoundedScalar S w U g ∧ ∀ x ∈ U, x ∉ coordDivisor S w →
      (g x)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧ G x ≤ g x • (1 : Matrix n n ℂ) := by sorry
