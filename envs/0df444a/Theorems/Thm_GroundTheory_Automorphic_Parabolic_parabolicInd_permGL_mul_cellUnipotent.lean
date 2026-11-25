-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul_cellUnipotent
-- name    : GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul_cellUnipotent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:12.232038+00:00
-- url     : https://prove2.me/theorems/4c5c359a-6d11-5f4c-8c98-96c8cb056363
-- title:
--   Parabolic: parabolic Ind perm GL mul cell Unipotent
-- statement:
--   The Parabolic construction uses the parabolic Ind perm GL mul cell Unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L98-L102

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

theorem GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul_cellUnipotent (f : parabolicIndSpace F n β σ)
    (a : cellUnipotent F β γ w) (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((a : GL (Fin n) F) * y)) =
      cellRepA β γ w σ a ((f : GL (Fin n) F → W) (permGL F w * y)) := by sorry
