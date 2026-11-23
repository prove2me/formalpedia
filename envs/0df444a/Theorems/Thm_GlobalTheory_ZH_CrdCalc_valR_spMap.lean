-- Prove2me | Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_spMap
-- name    : GlobalTheory.ZH.CrdCalc.valR_spMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:56.56092+00:00
-- url     : https://prove2.me/theorems/bcff5aa1-3389-42d5-ba18-0a820fa36ba0
-- title:
--   Crd Calc: val R sp Map
-- statement:
--   The Crd Calc construction uses the val R sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L36-L47

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

theorem GlobalTheory.ZH.CrdCalc.valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by sorry
