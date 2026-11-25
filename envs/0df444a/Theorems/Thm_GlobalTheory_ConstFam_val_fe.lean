-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_val_fe
-- name    : GlobalTheory.ConstFam.val_fe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:12.885935+00:00
-- url     : https://prove2.me/theorems/da518878-962e-4405-adec-9621de7498c8
-- title:
--   Const Fam: val fe
-- statement:
--   The Const Fam construction uses the val fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L222-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L222-L276

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
include hW hG

theorem GlobalTheory.ConstFam.val_fe (α mu : a.D₀.X)
    (u u' : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.deltaφ P.toPre F j (e α) (e mu)) (DegPre.deltaε j)))
    (hu : u.IsGen) (hc : LB.Gen.Corr P.toPre.P.L _ _ _ _ (LB.pullGen P.toPre.P.L _ _ u (DegPre.zF P.toPre F).left)
      (DegPre.famMult P.toPre F j (e mu) (e α))) (hu' : u'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF P.toPre F).left) (z : Z) J₀ J, Good a.D₀.P.L z J₀ →
      Good P.toPre.P.L z J → val (feGen a.D₀ j mu α) (r ≫ (DegPre.prB P.toPre F).left ≫ φ) z J₀ =
        (∏ i, wVal w z J₀ J (r ≫ DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i) * val u' r z J)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF P.toPre F).left) {z : Z} {J} (hJ : Good P.toPre.P.L z J) :
    (val u r z J).val = constVal (r ≫ strF P.toPre F) z
      (toF (R := PowerSeries k) F PowerSeries.X ^ expo a j α mu) * (val u' r z J).val := by sorry
