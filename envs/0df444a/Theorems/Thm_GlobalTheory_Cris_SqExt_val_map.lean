-- Prove2me | Theorems.Thm_GlobalTheory_Cris_SqExt_val_map
-- name    : GlobalTheory.Cris.SqExt.val_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:35.312532+00:00
-- url     : https://prove2.me/theorems/8f8d8064-4dd2-4d4c-aff3-969108c5dc7b
-- title:
--   Sq Ext: val map
-- statement:
--   The Sq Ext construction uses the val map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L525-L546
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L525-L546

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

theorem GlobalTheory.Cris.SqExt.val_map (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B) (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Form s) :
    E'.val y' hy' f.1 = φ (E.val y hy f.1) := by sorry
