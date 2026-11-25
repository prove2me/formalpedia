-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_isFlatAn_iff_isConstMul
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.isFlatAn_iff_isConstMul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:32.270991+00:00
-- url     : https://prove2.me/theorems/af2b161e-1338-4c79-816c-01563bb8d873
-- title:
--   Flat: is Flat An iff is Const Mul
-- statement:
--   The Flat construction uses the is Flat An iff is Const Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L187-L190

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {Xo : Moduli D l} {c : Coeff l}
variable {O : Type} [CommRing O] {β : O →+* c.F}
attribute [instance] CptOver.field CptOver.acg CptOver.mod

theorem GlobalTheory.CompanionTheory.Ar.Flat.isFlatAn_iff_isConstMul (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) :
    IsFlatAn U τ τ (algebraMap c.F ℂ) (φ ℂ) FU i e ρ ↔ IsConstMul U τ φ FU i e ρ := by sorry
