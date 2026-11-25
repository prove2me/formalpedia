-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_detPow_eq_qs_zpow
-- name    : GroundTheory.Automorphic.GodementJacquet.detPow_eq_qs_zpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:52.204547+00:00
-- url     : https://prove2.me/theorems/6062c10e-a92a-47ef-8e2a-b11ed632d926
-- title:
--   Godement Jacquet: det Pow eq qs zpow
-- statement:
--   The Godement Jacquet construction uses the det Pow eq qs zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L190-L194

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

theorem GroundTheory.Automorphic.GodementJacquet.detPow_eq_qs_zpow (g : GL (Fin n) F) (s : ℂ) : detPow g s = qs F s ^ ordDet g := by sorry
