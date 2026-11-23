-- Prove2me | Theorems.Thm_GlobalTheory_Cris_SqExt_val_apply
-- name    : GlobalTheory.Cris.SqExt.val_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:07.497811+00:00
-- url     : https://prove2.me/theorems/dbc79c89-f3b9-4a7a-8ba6-1753894a1f30
-- title:
--   Sq Ext: val apply
-- statement:
--   The Sq Ext construction uses the val apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L501-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L501-L502

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

theorem GlobalTheory.Cris.SqExt.val_apply (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) :
    E.val y hy f = ev f (E.secHom (E.red_w hy) E.i E.π_i) - ev f (E.idHom hy) := by sorry
