-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClopen_support_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.isClopen_support_parabolicInd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:34.80103+00:00
-- url     : https://prove2.me/theorems/734c6e7f-6388-4807-b059-e337d14be0be
-- title:
--   Parabolic: is Clopen support parabolic Ind
-- statement:
--   The Parabolic construction uses the is Clopen support parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L154-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L154-L176

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.Parabolic.isClopen_support_parabolicInd (f : parabolicIndSpace F n β σ) :
    IsClopen {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0} := by sorry
