-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul_cellLeviParabolic
-- name    : GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul_cellLeviParabolic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:06.657306+00:00
-- url     : https://prove2.me/theorems/53a8e414-feba-5d77-acfd-a6089e7dfd94
-- title:
--   Parabolic: parabolic Ind perm GL mul cell Levi Parabolic
-- statement:
--   The Parabolic construction uses the parabolic Ind perm GL mul cell Levi Parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L104-L108

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
variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))
variable {F β γ w}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul_cellLeviParabolic (f : parabolicIndSpace F n β σ)
    (b : cellLeviParabolic F β γ w) (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((b : GL (Fin n) F) * y)) =
      cellRepM β γ w σ b ((f : GL (Fin n) F → W) (permGL F w * y)) := by sorry
