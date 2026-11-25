-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_binomialSum_le
-- name    : GroundTheory.PAdicHodge.nrm_binomialSum_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:12.3398+00:00
-- url     : https://prove2.me/theorems/6caa55b7-e81b-4c4e-8477-1ad1ce5d7089
-- title:
--   PAdic Hodge: nrm binomial Sum le
-- statement:
--   The PAdic Hodge construction uses the nrm binomial Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L262-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L262-L266

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

theorem GroundTheory.PAdicHodge.nrm_binomialSum_le (x y : Ω) (hx : nrm K x ≤ 1) (hy : nrm K y ≤ 1) :
    nrm K (∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω)) ≤ 1 := by sorry
