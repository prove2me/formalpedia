-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_val_rig
-- name    : GlobalTheory.ConstFam.val_rig
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:32.732797+00:00
-- url     : https://prove2.me/theorems/bae685c3-de0f-4594-91ab-2ab9d9d26dda
-- title:
--   Const Fam: val rig
-- statement:
--   The Const Fam construction uses the val rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L158-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L158-L169

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
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x)
  {y : Sp F} {J₀ : (Sp F ⟶ a.D₀.P.A.left) → a.D₀.P.L.ι} {J : (Sp F ⟶ P.toPre.P.A.left) → P.toPre.P.L.ι}
  (hJ₀ : Good a.D₀.P.L y J₀) (hJ : Good P.toPre.P.L y J)
include hW hF hJ₀ hJ

theorem GlobalTheory.ConstFam.val_rig : val (L := a.D₀.P.L) a.D₀.rigK (jFK (R := k) F) y J₀ =
    wVal w y J₀ J (1 : TF (R := PowerSeries k) F ⟶ P.toPre.P.A).left *
      val (L := P.toPre.P.L) P.toPre.rigK (jFK (R := PowerSeries k) F) y J := by sorry
