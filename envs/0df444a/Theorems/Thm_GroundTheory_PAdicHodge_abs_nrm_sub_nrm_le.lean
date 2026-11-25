-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_abs_nrm_sub_nrm_le
-- name    : GroundTheory.PAdicHodge.abs_nrm_sub_nrm_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:19.133974+00:00
-- url     : https://prove2.me/theorems/575c9146-5392-4eb3-8a38-c8844ca0c9e7
-- title:
--   PAdic Hodge: abs nrm sub nrm le
-- statement:
--   The PAdic Hodge construction uses the abs nrm sub nrm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L109-L112

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {K}

theorem GroundTheory.PAdicHodge.abs_nrm_sub_nrm_le (x y : Ω) : |nrm K x - nrm K y| ≤ nrm K (x - y) := by sorry
