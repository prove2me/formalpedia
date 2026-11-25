-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_det_adLeviPar_of_diagonal
-- name    : GroundTheory.Automorphic.Parabolic.det_adLeviPar_of_diagonal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:47.832485+00:00
-- url     : https://prove2.me/theorems/6f56db58-febb-58f6-aa32-7510817d121d
-- title:
--   Parabolic: det ad Levi Par of diagonal
-- statement:
--   The Parabolic construction uses the det ad Levi Par of diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L276-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L276-L311

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

theorem GroundTheory.Automorphic.Parabolic.det_adLeviPar_of_diagonal (l : leviPar F n γ δ)
    (hl : ∀ i j, i ≠ j → ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    (LinearEquiv.det (adLeviPar F n γ δ l) : F) = ∏ s : LeviParIndex n γ δ,
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by sorry
