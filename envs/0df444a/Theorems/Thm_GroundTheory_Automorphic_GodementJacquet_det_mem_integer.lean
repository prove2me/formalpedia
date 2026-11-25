-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_det_mem_integer
-- name    : GroundTheory.Automorphic.GodementJacquet.det_mem_integer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:06.233503+00:00
-- url     : https://prove2.me/theorems/edcb48c6-566a-5a4d-a3b7-be8218d923de
-- title:
--   Godement Jacquet: det mem integer
-- statement:
--   The Godement Jacquet construction uses the det mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GodementJacquet.det_mem_integer {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    X.det ∈ 𝒪[F] := by sorry
