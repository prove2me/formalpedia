-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_one_add_pow_sub_one_le
-- name    : GroundTheory.PAdicHodge.nrm_one_add_pow_sub_one_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:40.389801+00:00
-- url     : https://prove2.me/theorems/2335d61e-fb6c-4df6-bbc3-035399fa66d2
-- title:
--   PAdic Hodge: nrm one add pow sub one le
-- statement:
--   The PAdic Hodge construction uses the nrm one add pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L301-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L301-L340

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
variable {p : ℕ}

theorem GroundTheory.PAdicHodge.nrm_one_add_pow_sub_one_le (hp : p.Prime) {w : Ω} (hw : nrm K w ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    nrm K ((1 + w) ^ (p ^ k) - 1) ≤ nrm K w * max (nrm K (p : Ω)) (nrm K w ^ (p - 1)) := by sorry
