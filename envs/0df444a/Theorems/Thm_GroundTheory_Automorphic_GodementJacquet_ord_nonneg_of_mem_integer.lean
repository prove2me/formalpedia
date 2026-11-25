-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_ord_nonneg_of_mem_integer
-- name    : GroundTheory.Automorphic.GodementJacquet.ord_nonneg_of_mem_integer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:19.136738+00:00
-- url     : https://prove2.me/theorems/01a11256-aaf4-592c-b890-ce030b61dc19
-- title:
--   Godement Jacquet: ord nonneg of mem integer
-- statement:
--   The Godement Jacquet construction uses the ord nonneg of mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L38-L39

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

theorem GroundTheory.Automorphic.GodementJacquet.ord_nonneg_of_mem_integer {x : F} (hx : x ∈ 𝒪[F]) (h0 : x ≠ 0) : 0 ≤ LocalField.ord x := by sorry
