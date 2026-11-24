-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_iteratedFDeriv_eq_zero_off
-- name    : GlobalTheory.ConvexCutOff.iteratedFDeriv_eq_zero_off
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:19.666544+00:00
-- url     : https://prove2.me/theorems/4492fca4-20bb-47aa-a1d3-c9f306a33dee
-- title:
--   Convex Cut Off: iterated FDeriv eq zero off
-- statement:
--   The Convex Cut Off construction uses the iterated FDeriv eq zero off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L100-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L100-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff

theorem GlobalTheory.ConvexCutOff.iteratedFDeriv_eq_zero_off {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (n : ℕ) : ∀ z, z ∉ K → iteratedFDeriv ℂ n F z = 0 := by sorry
