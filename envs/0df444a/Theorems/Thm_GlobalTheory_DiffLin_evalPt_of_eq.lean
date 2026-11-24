-- Prove2me | Theorems.Thm_GlobalTheory_DiffLin_evalPt_of_eq
-- name    : GlobalTheory.DiffLin.evalPt_of_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:21.008079+00:00
-- url     : https://prove2.me/theorems/31390092-3f73-4b28-9faa-02c45220d63f
-- title:
--   Diff Lin: eval Pt of eq
-- statement:
--   The Diff Lin construction uses the eval Pt of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsDiffSumSmulOfIsLieComb.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsDiffSumSmulOfIsLieComb.lean#L72-L77

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
open GlobalTheory.TangentOrigin

theorem GlobalTheory.DiffLin.evalPt_of_eq {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by sorry
