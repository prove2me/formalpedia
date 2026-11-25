-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isMaximalCompact_integralGL
-- name    : GroundTheory.Automorphic.GLnLocal.isMaximalCompact_integralGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:45.366614+00:00
-- url     : https://prove2.me/theorems/fca916ed-ea2f-45f2-89a2-1cef09ce9273
-- title:
--   GLn Local: is Maximal Compact integral GL
-- statement:
--   The GLn Local construction uses the is Maximal Compact integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L462-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L462-L463

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
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
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.isMaximalCompact_integralGL : IsMaximalCompact (integralGL F n) := by sorry
