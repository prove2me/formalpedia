-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_unipotentCompactG_of_isCompact
-- name    : GroundTheory.Automorphic.Parabolic.exists_unipotentCompactG_of_isCompact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:06.818445+00:00
-- url     : https://prove2.me/theorems/32710a1c-c7cf-4000-a3ee-e7c354641370
-- title:
--   Parabolic: exists unipotent Compact G of is Compact
-- statement:
--   The Parabolic construction uses the exists unipotent Compact G of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L217-L221

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
variable {γ : Fin n → ℕ}

theorem GroundTheory.Automorphic.Parabolic.exists_unipotentCompactG_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S)
    (hSN : S ⊆ unipotentRadical F n γ) :
    ∃ e : ℕ, S ⊆ (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by sorry
