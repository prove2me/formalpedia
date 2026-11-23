-- Prove2me | Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_map
-- name    : GlobalTheory.ZH.CrdCalc.crd_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:48.027675+00:00
-- url     : https://prove2.me/theorems/52345c79-9f57-4957-a786-be9b7399540e
-- title:
--   Crd Calc: crd map
-- statement:
--   The Crd Calc construction uses the crd map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L113-L120

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

theorem GlobalTheory.ZH.CrdCalc.crd_map {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by sorry
