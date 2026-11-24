-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_left_inv
-- name    : GlobalTheory.SW.HAct.left_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:09.810691+00:00
-- url     : https://prove2.me/theorems/858b0654-9ad9-4c39-a93c-0eaeaf9cd669
-- title:
--   HAct: left inv
-- statement:
--   The HAct construction uses the left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L140-L144

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

theorem GlobalTheory.SW.HAct.left_inv {γ : M2 E N} (h : γ ∈ UU E N) :
    -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) * γ = 1 := by sorry
