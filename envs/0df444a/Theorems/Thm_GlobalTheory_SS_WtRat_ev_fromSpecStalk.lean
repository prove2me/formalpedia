-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_ev_fromSpecStalk
-- name    : GlobalTheory.SS.WtRat.ev_fromSpecStalk
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:12.097427+00:00
-- url     : https://prove2.me/theorems/c97e741e-800a-4b0b-adc9-241ca8e3201f
-- title:
--   Wt Rat: ev from Spec Stalk
-- statement:
--   The Wt Rat construction uses the ev from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPoint.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPoint.lean#L22-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPoint
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {Y : Scheme.{0}}

theorem GlobalTheory.SS.WtRat.ev_fromSpecStalk (x : Y) {V : Y.Opens} (hx : x ∈ V)
    (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V) (u : Γ(Y, V)) :
    ev (R := Y.presheaf.stalk x) (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by sorry
