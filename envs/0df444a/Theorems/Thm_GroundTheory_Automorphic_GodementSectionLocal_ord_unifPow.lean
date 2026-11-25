-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_unifPow
-- name    : GroundTheory.Automorphic.GodementSectionLocal.ord_unifPow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:14.791645+00:00
-- url     : https://prove2.me/theorems/1e2da184-8b69-5262-9850-5236fa407d3b
-- title:
--   Godement Section Local: ord unif Pow
-- statement:
--   The Godement Section Local construction uses the ord unif Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L382-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L382-L382

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

theorem GroundTheory.Automorphic.GodementSectionLocal.ord_unifPow (k : ℤ) : ord ((unifPow k : Fˣ) : F) = k := by sorry
