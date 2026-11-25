-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow_sub_pow_le
-- name    : GroundTheory.PAdicHodge.nrm_pow_sub_pow_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:28.083733+00:00
-- url     : https://prove2.me/theorems/ee02d5e0-c182-4d88-aa23-43f24137c778
-- title:
--   PAdic Hodge: nrm pow sub pow le
-- statement:
--   The PAdic Hodge construction uses the nrm pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L240-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L240-L249

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

theorem GroundTheory.PAdicHodge.nrm_pow_sub_pow_le {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) (n : ℕ) :
    nrm K (a ^ n - b ^ n) ≤ nrm K (a - b) := by sorry
