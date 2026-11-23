-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_map_mem
-- name    : GlobalTheory.SW.HAct.map_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:29.652801+00:00
-- url     : https://prove2.me/theorems/5b1c4a7b-a41e-4e2d-b55b-10bddadd70cf
-- title:
--   HAct: map mem
-- statement:
--   The HAct construction uses the map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L180-L189

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

theorem GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by sorry
