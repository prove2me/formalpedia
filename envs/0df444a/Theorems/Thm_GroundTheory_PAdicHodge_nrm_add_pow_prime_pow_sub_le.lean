-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_pow_prime_pow_sub_le
-- name    : GroundTheory.PAdicHodge.nrm_add_pow_prime_pow_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:26.87887+00:00
-- url     : https://prove2.me/theorems/00bf65b9-1036-40b3-82a6-02ed193816a6
-- title:
--   PAdic Hodge: nrm add pow prime pow sub le
-- statement:
--   The PAdic Hodge construction uses the nrm add pow prime pow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L280-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L280-L299

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

theorem GroundTheory.PAdicHodge.nrm_add_pow_prime_pow_sub_le (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1)
    (hb : nrm K b ≤ 1) (k : ℕ) :
    nrm K ((a + b) ^ (p ^ k) - a ^ (p ^ k) - b ^ (p ^ k)) ≤ nrm K (p : Ω) := by sorry
