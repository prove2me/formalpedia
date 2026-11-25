-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_compactOpen_subgroupOf
-- name    : GroundTheory.Automorphic.Parabolic.exists_compactOpen_subgroupOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:03.504714+00:00
-- url     : https://prove2.me/theorems/5b9644dc-e583-4ce1-afe0-a15114940bb1
-- title:
--   Parabolic: exists compact Open subgroup Of
-- statement:
--   The Parabolic construction uses the exists compact Open subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L240-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L240-L256

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

theorem GroundTheory.Automorphic.Parabolic.exists_compactOpen_subgroupOf {H : Subgroup (GL (Fin n) F)}
    (hH : IsClosed (H : Set (GL (Fin n) F))) (hHN : H ≤ unipotentRadical F n γ)
    (s : Finset H) :
    ∃ K : Subgroup H, IsCompact (K : Set H) ∧ IsOpen (K : Set H) ∧ ∀ x ∈ s, x ∈ K := by sorry
