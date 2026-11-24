-- Prove2me | Theorems.Thm_GlobalTheory_Cris_SqExt_val_const
-- name    : GlobalTheory.Cris.SqExt.val_const
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:46.282804+00:00
-- url     : https://prove2.me/theorems/331295eb-4ba0-402b-a7c7-43d06e87b8c7
-- title:
--   Sq Ext: val const
-- statement:
--   The Sq Ext construction uses the val const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L635-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L635-L649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
attribute [instance] SqExt.ringC SqExt.ringB SqExt.algC SqExt.algB
open GlobalTheory.Cris.SqExt
variable {s : X ⟶ Sp R} (E E' : SqExt R)

theorem GlobalTheory.Cris.SqExt.val_const (x : Sp E.B ⟶ X) (hx : x ≫ s = spMap (algebraMap R E.B)) (y : Sp E.C ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R E.C)) (e : spMap (E.i : E.B →+* E.C) ≫ x = y) (f : Form s) :
    E.val y hy f.1 = 0 := by sorry
