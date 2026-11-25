-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_cellUnion
-- name    : GroundTheory.Automorphic.Parabolic.mem_cellUnion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:47.921+00:00
-- url     : https://prove2.me/theorems/18424365-066f-4ff7-8c1d-f6a0d3ff08a2
-- title:
--   Parabolic: mem cell Union
-- statement:
--   The Parabolic construction uses the mem cell Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L20-L21

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
variable {X : Type*} {k : ℕ} (C : Fin k → Set X)

theorem GroundTheory.Automorphic.Parabolic.mem_cellUnion {j : ℕ} {x : X} : x ∈ cellUnion C j ↔ ∃ l : Fin k, (l : ℕ) < j ∧ x ∈ C l := by sorry
