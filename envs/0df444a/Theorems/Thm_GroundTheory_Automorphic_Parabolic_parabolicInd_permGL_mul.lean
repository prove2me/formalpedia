-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul
-- name    : GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:29.02164+00:00
-- url     : https://prove2.me/theorems/4e4ee482-788b-5c75-a51e-eacf25a65432
-- title:
--   Parabolic: parabolic Ind perm GL mul
-- statement:
--   The Parabolic construction uses the parabolic Ind perm GL mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L45-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} (w : Equiv.Perm (Fin n))
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul (f : parabolicIndSpace F n β σ) (x : blockUpper F n (β ∘ w))
    (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((x : GL (Fin n) F) * y)) =
      cellRep β w σ x ((f : GL (Fin n) F → W) (permGL F w * y)) := by sorry
