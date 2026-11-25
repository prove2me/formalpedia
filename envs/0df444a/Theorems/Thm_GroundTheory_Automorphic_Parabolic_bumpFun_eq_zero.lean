-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_bumpFun_eq_zero
-- name    : GroundTheory.Automorphic.Parabolic.bumpFun_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:38.924089+00:00
-- url     : https://prove2.me/theorems/c0fae3b3-5a31-5df1-a37c-0215e6a6e87c
-- title:
--   Parabolic: bump Fun eq zero
-- statement:
--   The Parabolic construction uses the bump Fun eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L112-L117

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable {σ}

theorem GroundTheory.Automorphic.Parabolic.bumpFun_eq_zero {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    {g : GL (Fin n) F}
    (hg : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k) :
    bumpFun σ x K v g = 0 := by sorry
