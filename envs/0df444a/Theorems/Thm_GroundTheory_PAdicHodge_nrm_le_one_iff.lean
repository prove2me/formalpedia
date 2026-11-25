-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_one_iff
-- name    : GroundTheory.PAdicHodge.nrm_le_one_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:36.151608+00:00
-- url     : https://prove2.me/theorems/75397b14-4e29-43e3-8a1c-78cbc1c748e7
-- title:
--   PAdic Hodge: nrm le one iff
-- statement:
--   The PAdic Hodge construction uses the nrm le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L181-L182

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
variable [ValuativeRel Ω] [ValuativeExtension K Ω]

theorem GroundTheory.PAdicHodge.nrm_le_one_iff (x : Ω) : nrm K x ≤ 1 ↔ valuation Ω x ≤ 1 := by sorry
