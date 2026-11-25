-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_nrm_algebraMap_lt
-- name    : GroundTheory.PAdicHodge.exists_nrm_algebraMap_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:31.093306+00:00
-- url     : https://prove2.me/theorems/a9749177-e61b-53b2-9813-255945162678
-- title:
--   PAdic Hodge: exists nrm algebra Map lt
-- statement:
--   The PAdic Hodge construction uses the exists nrm algebra Map lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L159-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L159-L166

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
variable (K Ω)

theorem GroundTheory.PAdicHodge.exists_nrm_algebraMap_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ a : K, a ≠ 0 ∧ nrm K (algebraMap K Ω a) < ε := by sorry
