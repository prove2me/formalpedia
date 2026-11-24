-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_sumsAt_halfCurve
-- name    : GlobalTheory.Conv.exists_sumsAt_halfCurve
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:13.791991+00:00
-- url     : https://prove2.me/theorems/80385844-c638-4cce-b011-b74c295daeb4
-- title:
--   Conv: exists sums At half Curve
-- statement:
--   The Conv construction uses the exists sums At half Curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L161-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L161-L184

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

theorem GlobalTheory.Conv.exists_sumsAt_halfCurve {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {χ : Sp ℂ⟦X⟧ ⟶ Z}
    {F : Type} [Field F] (ι : ℂ⸨X⸩ →+* F)
    (hχ : spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) ≫ χ =
      spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y)
    {U : Z.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧
      ∀ f : Γ(Z, U), SumsAt (valR χ U f) w (valAt' (halfCurve yT w) U f) := by sorry
