-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_mem_integralGL
-- name    : GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:50.392797+00:00
-- url     : https://prove2.me/theorems/c25087f6-2614-5963-8187-de36e5a2df42
-- title:
--   Parabolic: perm GL mem integral GL
-- statement:
--   The Parabolic construction uses the perm GL mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L60-L72

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
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
  {n : ℕ}

theorem GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL (w : Equiv.Perm (Fin n)) : permGL F w ∈ integralGL F n := by sorry
