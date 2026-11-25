-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_eq_or_off
-- name    : GlobalTheory.ConstFam.eq_or_off
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:15.314957+00:00
-- url     : https://prove2.me/theorems/bf00edc0-9a28-4c37-8f40-8f4483929c36
-- title:
--   Const Fam: eq or off
-- statement:
--   The Const Fam construction uses the eq or off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstFamComponentsBasisExpansion.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstFamComponentsBasisExpansion.lean#L82-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion
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

theorem GlobalTheory.ConstFam.eq_or_off (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (j : ℕ) (α : a.D₀.X) (χ : P.toPre.X) :
    (∃ mu, e (α + j • mu) = χ) ∨ ∀ mu, e α + j • mu ≠ χ := by sorry
