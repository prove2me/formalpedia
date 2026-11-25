-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBounded_conj_of_isLogBounded
-- name    : GlobalTheory.IsLogBounded.conj_of_isLogBounded
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:18.86625+00:00
-- url     : https://prove2.me/theorems/487d7d53-c97d-4b3d-8e8e-8a6e0f24ce4f
-- title:
--   Is Log Bounded: conj of is Log Bounded
-- statement:
--   The Is Log Bounded construction uses the conj of is Log Bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L863-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L863-L869

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
variable [Fintype m]

theorem GlobalTheory.IsLogBounded.conj_of_isLogBounded (hG : IsLogBounded S w U G) {A : X → Matrix n m ℂ}
    (hA : IsLogBounded S w U fun x => (A x)ᴴ * A x) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x := by sorry
