-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_exists_valBall_subset
-- name    : GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:51.65258+00:00
-- url     : https://prove2.me/theorems/890f8d53-ea42-5f6c-a82e-3c81d3150e1b
-- title:
--   Godement Jacquet: exists val Ball subset
-- statement:
--   The Godement Jacquet construction uses the exists val Ball subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L67-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L67-L88

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

theorem GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset {S : Set (Matrix (Fin n) (Fin n) F)}
    (hS : S ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F)) :
    ∃ r : ℕ, {Y : Matrix (Fin n) (Fin n) F | ∀ i j, Y i j ∈ LocalField.valBall F r} ⊆ S := by sorry
