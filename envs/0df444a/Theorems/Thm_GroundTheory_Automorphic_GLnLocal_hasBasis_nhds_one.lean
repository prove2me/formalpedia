-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
-- name    : GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:30:56.717511+00:00
-- url     : https://prove2.me/theorems/dcbcb7ef-44ab-4a68-babd-dac346381560
-- title:
--   GLn Local: has Basis nhds one
-- statement:
--   The GLn Local construction uses the has Basis nhds one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L272-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L272-L296

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

theorem GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one :
    (𝓝 (1 : GL (Fin n) F)).HasBasis (fun _ : ℕ => True)
      fun m => (congruenceSubgroup F n m : Set (GL (Fin n) F)) := by sorry
