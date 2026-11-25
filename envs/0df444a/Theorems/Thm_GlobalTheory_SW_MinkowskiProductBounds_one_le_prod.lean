-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_one_le_prod
-- name    : GlobalTheory.SW.MinkowskiProductBounds.one_le_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:44.051046+00:00
-- url     : https://prove2.me/theorems/0b56e0e6-e56e-4ba5-8d73-7b200aa7b590
-- title:
--   Minkowski Product Bounds: one le prod
-- statement:
--   The Minkowski Product Bounds construction uses the one le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L80-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L80-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem GlobalTheory.SW.MinkowskiProductBounds.one_le_prod (h : IsType Ψ) {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) :
    1 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := by sorry
