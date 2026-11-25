-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_one_of_pow
-- name    : GroundTheory.PAdicHodge.nrm_le_one_of_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:01.312012+00:00
-- url     : https://prove2.me/theorems/60effd53-b35e-4436-9f34-703a8f5bcba4
-- title:
--   PAdic Hodge: nrm le one of pow
-- statement:
--   The PAdic Hodge construction uses the nrm le one of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L251-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L251-L252

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

theorem GroundTheory.PAdicHodge.nrm_le_one_of_pow {a : Ω} (ha : nrm K a ≤ 1) (n : ℕ) : nrm K (a ^ n) ≤ 1 := by sorry
