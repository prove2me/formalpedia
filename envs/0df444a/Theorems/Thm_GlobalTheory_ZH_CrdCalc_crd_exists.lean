-- Prove2me | Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_exists
-- name    : GlobalTheory.ZH.CrdCalc.crd_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:34.681633+00:00
-- url     : https://prove2.me/theorems/a7d8ac19-a0c5-4b66-9d2f-d167f2fbf61d
-- title:
--   Crd Calc: crd exists
-- statement:
--   The Crd Calc construction uses the crd exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L84-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem GlobalTheory.ZH.CrdCalc.crd_exists [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by sorry
