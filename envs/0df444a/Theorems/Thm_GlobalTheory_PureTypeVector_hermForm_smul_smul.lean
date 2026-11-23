-- Prove2me | Theorems.Thm_GlobalTheory_PureTypeVector_hermForm_smul_smul
-- name    : GlobalTheory.PureTypeVector.hermForm_smul_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:54.70208+00:00
-- url     : https://prove2.me/theorems/a27e82a4-9980-4213-bc1f-b59e75f2e413
-- title:
--   Pure Type Vector: herm Form smul smul
-- statement:
--   The Pure Type Vector construction uses the herm Form smul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/PureTypeVectorSpansQuadraticLattice.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/PureTypeVectorSpansQuadraticLattice.lean#L15-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_PureTypeVectorSpansQuadraticLattice
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
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.PureTypeVector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj

theorem GlobalTheory.PureTypeVector.hermForm_smul_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : ℂ) (u v : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • u) (w • v) = z * starRingEnd ℂ w * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u v := by sorry
