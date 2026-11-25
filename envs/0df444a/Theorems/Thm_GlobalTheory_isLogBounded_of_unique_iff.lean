-- Prove2me | Theorems.Thm_GlobalTheory_isLogBounded_of_unique_iff
-- name    : GlobalTheory.isLogBounded_of_unique_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:05.34282+00:00
-- url     : https://prove2.me/theorems/403b8d01-de5e-454a-b046-e24c57048ab9
-- title:
--   Global Theory: is Log Bounded of unique iff
-- statement:
--   The Global Theory construction uses the is Log Bounded of unique iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L813-L820
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L813-L820

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
omit [Fintype n]

theorem GlobalTheory.isLogBounded_of_unique_iff [Unique n] {g : X → ℝ} :
    (IsLogBounded S w U fun x => Matrix.of fun _ _ : n => (g x : ℂ)) ↔
      IsLogBoundedScalar S w U g := by sorry
