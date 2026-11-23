-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_le_preimage_inclusion
-- name    : GlobalTheory.Conv.exists_le_preimage_inclusion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:25.601221+00:00
-- url     : https://prove2.me/theorems/b6328220-e432-4a39-9bd6-7726de8d73a3
-- title:
--   Conv: exists le preimage inclusion
-- statement:
--   The Conv construction uses the exists le preimage inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L85-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L85-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
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

theorem GlobalTheory.Conv.exists_le_preimage_inclusion {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) ⁻¹ᵁ U) :
    ∃ T', ∃ h : T ≤ T', ⊤ ≤ (spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') ≫ yT) ⁻¹ᵁ U := by sorry
