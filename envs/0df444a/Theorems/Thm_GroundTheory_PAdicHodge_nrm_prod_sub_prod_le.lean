-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod_sub_prod_le
-- name    : GroundTheory.PAdicHodge.nrm_prod_sub_prod_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:49.363851+00:00
-- url     : https://prove2.me/theorems/0f1e2539-0c17-44df-931d-482dc179fcd4
-- title:
--   PAdic Hodge: nrm prod sub prod le
-- statement:
--   The PAdic Hodge construction uses the nrm prod sub prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L213-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L213-L238

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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem GroundTheory.PAdicHodge.nrm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, nrm K (a i) ≤ 1) (hb : ∀ i ∈ s, nrm K (b i) ≤ 1)
    (h : ∀ i ∈ s, nrm K (a i - b i) ≤ δ) :
    nrm K (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ δ := by sorry
