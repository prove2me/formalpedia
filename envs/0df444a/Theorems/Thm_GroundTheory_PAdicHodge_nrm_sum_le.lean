-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_sum_le
-- name    : GroundTheory.PAdicHodge.nrm_sum_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:44.693667+00:00
-- url     : https://prove2.me/theorems/3415044b-5c3d-4f66-a0a9-ef45c10dd39d
-- title:
--   PAdic Hodge: nrm sum le
-- statement:
--   The PAdic Hodge construction uses the nrm sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L127-L135

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

theorem GroundTheory.PAdicHodge.nrm_sum_le {ι : Type*} {s : Finset ι} {f : ι → Ω} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, nrm K (f i) ≤ C) : nrm K (∑ i ∈ s, f i) ≤ C := by sorry
