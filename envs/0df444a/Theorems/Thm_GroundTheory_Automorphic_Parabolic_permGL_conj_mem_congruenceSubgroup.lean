-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_conj_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:19.366775+00:00
-- url     : https://prove2.me/theorems/9de672d0-a4e4-5407-84fb-72c2c83946a2
-- title:
--   Parabolic: perm GL conj mem congruence Subgroup
-- statement:
--   The Parabolic construction uses the perm GL conj mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L182-L185

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup {J : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ congruenceSubgroup F n J) :
    permGL F w * k * (permGL F w)⁻¹ ∈ congruenceSubgroup F n J := by sorry
