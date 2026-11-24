-- Prove2me | Theorems.Thm_GlobalTheory_DiffLin_top_le_preimage_of_dualLift
-- name    : GlobalTheory.DiffLin.top_le_preimage_of_dualLift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:30.761225+00:00
-- url     : https://prove2.me/theorems/5dc9be41-5117-4b5f-96ab-8d32a878d40d
-- title:
--   Diff Lin: top le preimage of dual Lift
-- statement:
--   The Diff Lin construction uses the top le preimage of dual Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsDiffSumSmulOfIsLieComb.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsDiffSumSmulOfIsLieComb.lean#L64-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.DiffLin.top_le_preimage_of_dualLift {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (t : Fin n → R)
    (h : ⊤ ≤ (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by sorry
