-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_inv_conj_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.permGL_inv_conj_mem_congruenceSubgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:13.010714+00:00
-- url     : https://prove2.me/theorems/882401d0-dced-5159-97bb-12784afce83b
-- title:
--   Parabolic: perm GL inv conj mem congruence Subgroup
-- statement:
--   The Parabolic construction uses the perm GL inv conj mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L187-L191

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

theorem GroundTheory.Automorphic.Parabolic.permGL_inv_conj_mem_congruenceSubgroup {J : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ congruenceSubgroup F n J) :
    (permGL F w)⁻¹ * k * permGL F w ∈ congruenceSubgroup F n J := by sorry
