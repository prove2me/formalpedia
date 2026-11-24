-- Prove2me | Theorems.Thm_GlobalTheory_GenericConnected_not_mem_image_inter
-- name    : GlobalTheory.GenericConnected.not_mem_image_inter
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:08.044746+00:00
-- url     : https://prove2.me/theorems/c3dbd7c9-5092-4e87-873b-b70457512879
-- title:
--   Generic Connected: not mem image inter
-- statement:
--   The Generic Connected construction uses the not mem image inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedGenericFibreOfDense.lean#L158-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedGenericFibreOfDense.lean#L158-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory GlobalTheory.GenericConnected

theorem GlobalTheory.GenericConnected.not_mem_image_inter {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : GeometricallyConnected (f.fiberToSpecResidueField (t y)))
    (U V : (pullback f t).Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    y ∉ (pullback.snd f t '' U) ∩ (pullback.snd f t '' V) := by sorry
