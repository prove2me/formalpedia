-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_unitVal_linComb
-- name    : GlobalTheory.PullHermitian.unitVal_linComb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:25.948881+00:00
-- url     : https://prove2.me/theorems/da01dc15-f925-445a-bf92-6610f5c85179
-- title:
--   Pull Hermitian: unit Val lin Comb
-- statement:
--   The Pull Hermitian construction uses the unit Val lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L61-L71

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

theorem GlobalTheory.PullHermitian.unitVal_linComb {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (ε : ℤ) (j j' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j) ⊓
      (L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j')))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    unitVal x h ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).g (fun _ => j) (fun _ => j')) =
      unitVal (x ≫ φ) h' (L.g j j') ^ ε := by sorry
