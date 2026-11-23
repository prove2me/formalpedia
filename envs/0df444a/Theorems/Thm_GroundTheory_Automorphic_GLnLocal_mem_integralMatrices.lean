-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_integralMatrices
-- name    : GroundTheory.Automorphic.GLnLocal.mem_integralMatrices
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:31.327622+00:00
-- url     : https://prove2.me/theorems/824c9186-3a83-4287-b316-2ee33f42da03
-- title:
--   GLn Local: mem integral Matrices
-- statement:
--   The GLn Local construction uses the mem integral Matrices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L19-L25

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

theorem GroundTheory.Automorphic.GLnLocal.mem_integralMatrices {A : Matrix (Fin n) (Fin n) F} :
    A ∈ integralMatrices F n ↔ ∀ i j, A i j ∈ 𝒪[F] := by sorry
