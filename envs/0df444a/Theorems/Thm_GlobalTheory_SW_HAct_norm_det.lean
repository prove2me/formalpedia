-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_norm_det
-- name    : GlobalTheory.SW.HAct.norm_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:35.868077+00:00
-- url     : https://prove2.me/theorems/14b229c6-a562-432f-a411-bf6d226b6cd5
-- title:
--   HAct: norm det
-- statement:
--   The HAct construction uses the norm det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L191-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L191-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.HAct.norm_det (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) : ‖τ γ.det‖ = 1 := by sorry
