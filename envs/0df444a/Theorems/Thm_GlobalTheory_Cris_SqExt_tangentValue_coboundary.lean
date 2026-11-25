-- Prove2me | Theorems.Thm_GlobalTheory_Cris_SqExt_tangentValue_coboundary
-- name    : GlobalTheory.Cris.SqExt.tangentValue_coboundary
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:07.328668+00:00
-- url     : https://prove2.me/theorems/42a4c58d-cce0-59d1-aba1-ff5897b553f3
-- title:
--   Sq Ext: tangent Value coboundary
-- statement:
--   The Sq Ext construction uses the tangent Value coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L504-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L504-L510

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

theorem GlobalTheory.Cris.SqExt.tangentValue_coboundary (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (g : C0 (O (dp0 R) s)) :
    E.val y hy ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ =
      (g (Thick.triv E.C y hy) : E.C) - E.i (g (Thick.triv E.B _ (E.red_w hy))) := by sorry
