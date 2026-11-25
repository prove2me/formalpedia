-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod
-- name    : GroundTheory.PAdicHodge.nrm_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:04:56.924853+00:00
-- url     : https://prove2.me/theorems/b5ea6a6a-c0e9-4ae2-8010-abb47984d5d6
-- title:
--   PAdic Hodge: nrm prod
-- statement:
--   The PAdic Hodge construction uses the nrm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L121-L125

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

theorem GroundTheory.PAdicHodge.nrm_prod {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    nrm K (∏ i ∈ s, f i) = ∏ i ∈ s, nrm K (f i) := by sorry
