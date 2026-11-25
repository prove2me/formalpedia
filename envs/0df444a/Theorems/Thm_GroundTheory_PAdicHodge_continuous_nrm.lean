-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_continuous_nrm
-- name    : GroundTheory.PAdicHodge.continuous_nrm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:44.665794+00:00
-- url     : https://prove2.me/theorems/ece259bc-94fb-446f-bc91-d9d059c3ad8b
-- title:
--   PAdic Hodge: continuous nrm
-- statement:
--   The PAdic Hodge construction uses the continuous nrm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L191-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L191-L204

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
variable [TopologicalSpace Ω] [IsValuativeTopology Ω]
variable (K Ω)

theorem GroundTheory.PAdicHodge.continuous_nrm : Continuous (nrm K : Ω → ℝ) := by sorry
