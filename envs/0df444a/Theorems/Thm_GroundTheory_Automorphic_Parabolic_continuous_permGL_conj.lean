-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_continuous_permGL_conj
-- name    : GroundTheory.Automorphic.Parabolic.continuous_permGL_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:38.236488+00:00
-- url     : https://prove2.me/theorems/395c6a23-9a76-5ae0-8b09-fb25d911997b
-- title:
--   Parabolic: continuous perm GL conj
-- statement:
--   The Parabolic construction uses the continuous perm GL conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L194-L196

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.Parabolic.continuous_permGL_conj (w : Equiv.Perm (Fin n)) :
    Continuous fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹ := by sorry
