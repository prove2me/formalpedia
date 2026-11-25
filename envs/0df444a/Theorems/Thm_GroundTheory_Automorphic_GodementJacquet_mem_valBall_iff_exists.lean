-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_valBall_iff_exists
-- name    : GroundTheory.Automorphic.GodementJacquet.mem_valBall_iff_exists
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:14.213805+00:00
-- url     : https://prove2.me/theorems/fee5bc50-211c-5166-ac50-b6251907b91c
-- title:
--   Godement Jacquet: mem val Ball iff exists
-- statement:
--   The Godement Jacquet construction uses the mem val Ball iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L44-L65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
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
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.GodementJacquet.mem_valBall_iff_exists {r : ℕ} {y : F} :
    y ∈ LocalField.valBall F r ↔ ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a := by sorry
