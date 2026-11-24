-- Prove2me | Theorems.Thm_GlobalTheory_Cris_SqExt_val_pull
-- name    : GlobalTheory.Cris.SqExt.val_pull
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:46.458896+00:00
-- url     : https://prove2.me/theorems/8ee5eb9a-5770-4fa4-a950-f263ee23b338
-- title:
--   Sq Ext: val pull
-- statement:
--   The Sq Ext construction uses the val pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L548-L587
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L548-L587

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

theorem GlobalTheory.Cris.SqExt.val_pull {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : IsMor (dp0 R) s (dp0 R) s' (RingHom.id R) φ)
    (y : Sp E.C ⟶ X') (hy : y ≫ s' = spMap (algebraMap R E.C))
    (hy' : (y ≫ φ) ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.val y hy (h.pullForm f).1 = E.val (y ≫ φ) hy' f.1 := by sorry
