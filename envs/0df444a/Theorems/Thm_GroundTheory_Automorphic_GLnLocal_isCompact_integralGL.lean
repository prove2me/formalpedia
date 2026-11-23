-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
-- name    : GroundTheory.Automorphic.GLnLocal.isCompact_integralGL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:10.653326+00:00
-- url     : https://prove2.me/theorems/ab046d7b-ebe8-44e7-929a-2a9583817382
-- title:
--   GLn Local: is Compact integral GL
-- statement:
--   The GLn Local construction uses the is Compact integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L157-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L157-L168

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.isCompact_integralGL : IsCompact (integralGL F n : Set (GL (Fin n) F)) := by sorry
