-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_pow_le
-- name    : GroundTheory.PAdicHodge.NormTower.nrm_N_sub_pow_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:00.155506+00:00
-- url     : https://prove2.me/theorems/b10917e1-a0b3-4a89-a9f4-a95a4c4c54a1
-- title:
--   Norm Tower: nrm N sub pow le
-- statement:
--   The Norm Tower construction uses the nrm N sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L434-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L434-L441

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
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)

theorem GroundTheory.PAdicHodge.NormTower.nrm_N_sub_pow_le (n : ℕ) {y : Ω} (hy : y ∈ t.E (n + 1)) (hy1 : nrm K y ≤ 1) :
    nrm K (t.N n y - y ^ (p ^ t.k n)) ≤ t.c := by sorry
