-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_wchart_of
-- name    : GlobalTheory.PullHermitian.wchart_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:33.268389+00:00
-- url     : https://prove2.me/theorems/8b2e3021-f46c-498b-bec5-284b226c2190
-- title:
--   Pull Hermitian: wchart of
-- statement:
--   The Pull Hermitian construction uses the wchart of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L47-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
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
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem GlobalTheory.PullHermitian.wchart_of {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (j : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart (K := PUnit) (fun _ => φ) (fun _ => j) := by sorry
