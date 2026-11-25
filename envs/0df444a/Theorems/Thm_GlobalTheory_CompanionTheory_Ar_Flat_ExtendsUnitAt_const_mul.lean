-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ExtendsUnitAt_const_mul
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.const_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:09.78986+00:00
-- url     : https://prove2.me/theorems/a3822a01-6af7-4a26-9cf2-4fd70f9e8e2e
-- title:
--   Extends Unit At: const mul
-- statement:
--   The Extends Unit At construction uses the const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L207-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L207-L214

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.const_mul {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X}
    (h : ExtendsUnitAt s σ ξ W F t x) {k : ℂ} (hk : k ≠ 0) : ExtendsUnitAt s σ ξ W (fun y => k * F y) t x := by sorry
