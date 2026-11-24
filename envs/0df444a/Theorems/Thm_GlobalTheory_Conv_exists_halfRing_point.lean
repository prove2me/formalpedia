-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_halfRing_point
-- name    : GlobalTheory.Conv.exists_halfRing_point
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:38.857789+00:00
-- url     : https://prove2.me/theorems/1789c91e-09b6-4be3-b9d3-49db546dbf41
-- title:
--   Conv: exists half Ring point
-- statement:
--   The Conv construction uses the exists half Ring point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L51-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L51-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}

theorem GlobalTheory.Conv.exists_halfRing_point {O : Type} [CommRing O] (s : Z ⟶ Sp O) [LocallyOfFiniteType s]
    (b : O →+* ℂ) (y : Sp convLaurent ⟶ Z)
    (hy : y ≫ s = spMap ((algebraMap ℂ convLaurent).comp b)) {V : Z.Opens} (hV : IsAffineOpen V)
    (hyV : ⊤ ≤ y ⁻¹ᵁ V) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ yT : Sp (halfRing T) ⟶ Z, ⊤ ≤ yT ⁻¹ᵁ V ∧
      spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y ∧
      yT ≫ s = spMap ((algebraMap ℂ (halfRing T)).comp b) := by sorry
