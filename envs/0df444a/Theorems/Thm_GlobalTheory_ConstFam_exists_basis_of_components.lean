-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_exists_basis_of_components
-- name    : GlobalTheory.ConstFam.exists_basis_of_components
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:18.393984+00:00
-- url     : https://prove2.me/theorems/e59a6552-5586-4514-bafd-bf98d14a65f5
-- title:
--   Const Fam: exists basis of components
-- statement:
--   The Const Fam construction uses the exists basis of components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsBasisOfIsExtension.lean#L42-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsBasisOfIsExtension.lean#L42-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
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

theorem GlobalTheory.ConstFam.exists_basis_of_components {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M] {C : Type}
    [Finite C] {W : C → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module L (W x)] (p : ∀ x, M →ₗ[L] W x)
    (inj : ∀ m, (∀ x, p x m = 0) → m = 0) {Idx : C → Type} (bs : ∀ x, Module.Basis (Idx x) L (W x))
    (v : ∀ x, Idx x → M) (h₁ : ∀ x i, p x (v x i) = bs x i) (h₂ : ∀ x y i, y ≠ x → p y (v x i) = 0) :
    ∃ B : Module.Basis (Σ x, Idx x) L M, ∀ x i, B ⟨x, i⟩ = v x i := by sorry
