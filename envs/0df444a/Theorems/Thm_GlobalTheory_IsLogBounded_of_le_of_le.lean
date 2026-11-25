-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBounded_of_le_of_le
-- name    : GlobalTheory.IsLogBounded.of_le_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:41.744062+00:00
-- url     : https://prove2.me/theorems/3317c416-f706-4f9c-acc3-bc015e396df6
-- title:
--   Is Log Bounded: of le of le
-- statement:
--   The Is Log Bounded construction uses the of le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L743-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L743-L754

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
open GlobalTheory.IsLogBounded

theorem GlobalTheory.IsLogBounded.of_le_of_le {G₁ G₂ : X → Matrix n n ℂ} (h₁ : IsLogBounded S w U G₁)
    (h₂ : IsLogBounded S w U G₂) (h : ∀ x ∈ U, x ∉ coordDivisor S w → G₁ x ≤ G x ∧ G x ≤ G₂ x) :
    IsLogBounded S w U G := by sorry
