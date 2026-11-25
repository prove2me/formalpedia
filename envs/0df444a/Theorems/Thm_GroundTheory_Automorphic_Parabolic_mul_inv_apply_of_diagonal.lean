-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_inv_apply_of_diagonal
-- name    : GroundTheory.Automorphic.Parabolic.mul_inv_apply_of_diagonal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:39.440808+00:00
-- url     : https://prove2.me/theorems/51958fd1-a5d7-467c-a33f-11852120ad8f
-- title:
--   Parabolic: mul inv apply of diagonal
-- statement:
--   The Parabolic construction uses the mul inv apply of diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L246-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L246-L255

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}

theorem GroundTheory.Automorphic.Parabolic.mul_inv_apply_of_diagonal {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) F) i i * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (1 : Matrix (Fin n) (Fin n) F) i j := by sorry
