-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_integralGL_eq_units
-- name    : GroundTheory.Automorphic.GLnLocal.integralGL_eq_units
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:51.662656+00:00
-- url     : https://prove2.me/theorems/9c9a275c-82c4-4bb3-986f-223643fbb183
-- title:
--   GLn Local: integral GL eq units
-- statement:
--   The GLn Local construction uses the integral GL eq units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L64-L67

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

theorem GroundTheory.Automorphic.GLnLocal.integralGL_eq_units : integralGL F n = (integralMatrices F n).toSubmonoid.units := by sorry
