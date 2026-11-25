-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_levi_eq_mul
-- name    : GroundTheory.Automorphic.Parabolic.exists_finset_levi_eq_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:06.275579+00:00
-- url     : https://prove2.me/theorems/2a735f56-dacb-5d54-b713-89b30ccc457e
-- title:
--   Parabolic: exists finset levi eq mul
-- statement:
--   The Parabolic construction uses the exists finset levi eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L300-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L300-L330

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem GroundTheory.Automorphic.Parabolic.exists_finset_levi_eq_mul (j : ℕ) :
    ∃ T : Finset (GL (Fin n) F), (∀ t ∈ T, t ∈ levi F n γ ⊓ integralGL F n) ∧
      ∀ m ∈ levi F n γ, ∃ b ∈ cellLeviParabolic F β γ w, ∃ t ∈ T,
        ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n j, m = b * t * k := by sorry
