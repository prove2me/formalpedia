-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_eq_left
-- name    : GroundTheory.PAdicHodge.nrm_add_eq_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:47.183178+00:00
-- url     : https://prove2.me/theorems/197d8a7c-6757-46c8-ac15-dc3130b8cb01
-- title:
--   PAdic Hodge: nrm add eq left
-- statement:
--   The PAdic Hodge construction uses the nrm add eq left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean#L114-L119

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

theorem GroundTheory.PAdicHodge.nrm_add_eq_left {x y : Ω} (h : nrm K y < nrm K x) : nrm K (x + y) = nrm K x := by sorry
