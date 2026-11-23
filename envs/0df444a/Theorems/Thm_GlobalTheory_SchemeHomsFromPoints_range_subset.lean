-- Prove2me | Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_range_subset
-- name    : GlobalTheory.SchemeHomsFromPoints.range_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:58.681945+00:00
-- url     : https://prove2.me/theorems/52a8b7f0-4d67-441b-b2af-2dacc122061b
-- title:
--   Scheme Homs From Points: range subset
-- statement:
--   The Scheme Homs From Points construction uses the range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L66-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints

theorem GlobalTheory.SchemeHomsFromPoints.range_subset {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Set.range x ⊆ Set.range W.ι := by sorry
