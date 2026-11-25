-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_bumpFun_apply
-- name    : GroundTheory.Automorphic.Parabolic.bumpFun_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:50.217477+00:00
-- url     : https://prove2.me/theorems/3555a365-ea46-4240-b241-ae365086fdd6
-- title:
--   Parabolic: bump Fun apply
-- statement:
--   The Parabolic construction uses the bump Fun apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L87-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L87-L110

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

theorem GroundTheory.Automorphic.Parabolic.bumpFun_apply {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ K.map (MulAut.conj x).toMonoidHom →
      inflateTwist F n β σ p v = v)
    (p : blockUpper F n β) {k : GL (Fin n) F} (hk : k ∈ K) :
    bumpFun σ x K v ((p : GL (Fin n) F) * x * k) = inflateTwist F n β σ p v := by sorry
