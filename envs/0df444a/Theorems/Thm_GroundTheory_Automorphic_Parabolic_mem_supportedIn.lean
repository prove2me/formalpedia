-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_supportedIn
-- name    : GroundTheory.Automorphic.Parabolic.mem_supportedIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:57.404336+00:00
-- url     : https://prove2.me/theorems/ccd99a04-cd09-5784-8a4f-47de6926a5ff
-- title:
--   Parabolic: mem supported In
-- statement:
--   The Parabolic construction uses the mem supported In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L199-L201

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
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
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} (γ : Fin n → ℕ)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {σ}

theorem GroundTheory.Automorphic.Parabolic.mem_supportedIn {Y : Set (GL (Fin n) F)} {f : parabolicIndSpace F n β σ} :
    f ∈ supportedIn σ Y ↔ ∀ g ∉ Y, (f : GL (Fin n) F → W) g = 0 := by sorry
