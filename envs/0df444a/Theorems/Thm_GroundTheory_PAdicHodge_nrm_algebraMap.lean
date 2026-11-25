-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_algebraMap
-- name    : GroundTheory.PAdicHodge.nrm_algebraMap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:49.271232+00:00
-- url     : https://prove2.me/theorems/86f5edb5-b1d3-5555-aec3-f1bf79fe0393
-- title:
--   PAdic Hodge: nrm algebra Map
-- statement:
--   The PAdic Hodge construction uses the nrm algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L137-L139

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

theorem GroundTheory.PAdicHodge.nrm_algebraMap (a : K) : nrm K (algebraMap K Ω a) = (letI := normedField K; ‖a‖) := by sorry
