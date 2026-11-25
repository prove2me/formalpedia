-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_subgroupOf_cellUnipotent
-- name    : GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_cellUnipotent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:43.289459+00:00
-- url     : https://prove2.me/theorems/5af931ae-8947-542f-a4d8-9f31faae7a22
-- title:
--   Parabolic: is Compact subgroup Of cell Unipotent
-- statement:
--   The Parabolic construction uses the is Compact subgroup Of cell Unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
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
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_cellUnipotent (e : ℕ) :
    IsCompact (((unipotentCompactG (F := F) γ e).subgroupOf (cellUnipotent F β γ w) :
      Subgroup (cellUnipotent F β γ w)) : Set (cellUnipotent F β γ w)) := by sorry
