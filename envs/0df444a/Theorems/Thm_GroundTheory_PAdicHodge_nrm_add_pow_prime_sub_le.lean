-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_pow_prime_sub_le
-- name    : GroundTheory.PAdicHodge.nrm_add_pow_prime_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:43.482001+00:00
-- url     : https://prove2.me/theorems/f0bd5ffb-2213-58f5-9d1b-378025404ba0
-- title:
--   PAdic Hodge: nrm add pow prime sub le
-- statement:
--   The PAdic Hodge construction uses the nrm add pow prime sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L268-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L268-L278

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

theorem GroundTheory.PAdicHodge.nrm_add_pow_prime_sub_le (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) :
    nrm K ((a + b) ^ p - a ^ p - b ^ p) ≤ nrm K (p : Ω) := by sorry
