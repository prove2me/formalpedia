-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_mem_box
-- name    : GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_box
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:54.655223+00:00
-- url     : https://prove2.me/theorems/0a9fe264-d7fc-4a86-9845-210b6b93c950
-- title:
--   Godement Section Local: vec Mul mem box
-- statement:
--   The Godement Section Local construction uses the vec Mul mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L703-L710
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L703-L710

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]

theorem GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_box {k : GL (Fin 2) F} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F])
    {n : ℤ} {x : Fin 2 → F} (hx : x ∈ box F n) :
    x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ box F n := by sorry
