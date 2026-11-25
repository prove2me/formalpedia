-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellUnipotent_le_unipotentRadical
-- name    : GroundTheory.Automorphic.Parabolic.cellUnipotent_le_unipotentRadical
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:50.232813+00:00
-- url     : https://prove2.me/theorems/456f41f6-6695-45a8-b61c-d16a262191a0
-- title:
--   Parabolic: cell Unipotent le unipotent Radical
-- statement:
--   The Parabolic construction uses the cell Unipotent le unipotent Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L71-L72

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
variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))
variable {F β γ w}

theorem GroundTheory.Automorphic.Parabolic.cellUnipotent_le_unipotentRadical : cellUnipotent F β γ w ≤ unipotentRadical F n γ := by sorry
