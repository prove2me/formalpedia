-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_inv
-- name    : GroundTheory.PAdicHodge.nrm_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:30.361373+00:00
-- url     : https://prove2.me/theorems/f9732162-604f-4619-a388-b67ade044e39
-- title:
--   PAdic Hodge: nrm inv
-- statement:
--   The PAdic Hodge construction uses the nrm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L75-L78

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

theorem GroundTheory.PAdicHodge.nrm_inv (x : Ω) : nrm K x⁻¹ = (nrm K x)⁻¹ := by sorry
