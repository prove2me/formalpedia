-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_supportedIn_le_comap
-- name    : GroundTheory.Automorphic.Parabolic.supportedIn_le_comap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:29.491074+00:00
-- url     : https://prove2.me/theorems/744a11d7-14df-486c-a104-3d1c9c6858cd
-- title:
--   Parabolic: supported In le comap
-- statement:
--   The Parabolic construction uses the supported In le comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L220-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L220-L230

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

theorem GroundTheory.Automorphic.Parabolic.supportedIn_le_comap {Y : Set (GL (Fin n) F)}
    (hY : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {q : GL (Fin n) F}
    (hq : q ∈ blockUpper F n γ) :
    supportedIn σ Y ≤ (supportedIn σ Y).comap (parabolicInd F n β σ q) := by sorry
