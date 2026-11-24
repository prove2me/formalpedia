-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_congruenceSubgroup
-- name    : GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:59.978803+00:00
-- url     : https://prove2.me/theorems/40724498-95c4-410a-8772-2f5583a550be
-- title:
--   GLn Local: is Compact congruence Subgroup
-- statement:
--   The GLn Local construction uses the is Compact congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L257-L260

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

theorem GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup (m : ℕ) :
    IsCompact (congruenceSubgroup F n m : Set (GL (Fin n) F)) := by sorry
