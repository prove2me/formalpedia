-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_cellUnipotent
-- name    : GroundTheory.Automorphic.Parabolic.isClosed_cellUnipotent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:11.911653+00:00
-- url     : https://prove2.me/theorems/f7954466-cb84-4027-860c-638237ac2a60
-- title:
--   Parabolic: is Closed cell Unipotent
-- statement:
--   The Parabolic construction uses the is Closed cell Unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L258-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L258-L260

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

theorem GroundTheory.Automorphic.Parabolic.isClosed_cellUnipotent {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} :
    IsClosed (cellUnipotent F β γ w : Set (GL (Fin n) F)) := by sorry
