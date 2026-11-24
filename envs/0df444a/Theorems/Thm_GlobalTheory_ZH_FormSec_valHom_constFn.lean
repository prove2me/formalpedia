-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FormSec_valHom_constFn
-- name    : GlobalTheory.ZH.FormSec.valHom_constFn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:02:22.880787+00:00
-- url     : https://prove2.me/theorems/395227d4-a03c-4c31-b5ea-9b6db82fbf75
-- title:
--   Form Sec: val Hom const Fn
-- statement:
--   The Form Sec construction uses the val Hom const Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L93-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L93-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFormSec
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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.FormSec
open scoped Pointwise

theorem GlobalTheory.ZH.FormSec.valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by sorry
