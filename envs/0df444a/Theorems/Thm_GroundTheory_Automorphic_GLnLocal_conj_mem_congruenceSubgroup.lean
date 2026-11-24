-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.GLnLocal.conj_mem_congruenceSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:56.74971+00:00
-- url     : https://prove2.me/theorems/ebc8e0ef-7ba1-44d6-a6ff-e123b5147247
-- title:
--   GLn Local: conj mem congruence Subgroup
-- statement:
--   The GLn Local construction uses the conj mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L228-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L228-L232

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

theorem GroundTheory.Automorphic.GLnLocal.conj_mem_congruenceSubgroup {m : ℕ} {k x : GL (Fin n) F} (hk : k ∈ integralGL F n)
    (hx : x ∈ congruenceSubgroup F n m) : k * x * k⁻¹ ∈ congruenceSubgroup F n m := by sorry
