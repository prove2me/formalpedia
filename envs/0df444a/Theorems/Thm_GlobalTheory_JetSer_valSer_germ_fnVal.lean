-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_valSer_germ_fnVal
-- name    : GlobalTheory.JetSer.valSer_germ_fnVal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.052342+00:00
-- url     : https://prove2.me/theorems/bcb08c71-a3e6-40e1-b53c-432934ad49cd
-- title:
--   Jet Ser: val Ser germ fn Val
-- statement:
--   The Jet Ser construction uses the val Ser germ fn Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ValSerGermFnVal.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ValSerGermFnVal.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.valSer_germ_fnVal {A : Type} [CommRing A] {Y : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Spec (CommRingCat.of A)) (f : Γ(Y, U)) :
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U f)) = gs r z U f := by sorry
