-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ExtendsUnitAt_eq_zero_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.eq_zero_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:51.707524+00:00
-- url     : https://prove2.me/theorems/29428f67-73f8-5819-bbcb-e910ca8c1607
-- title:
--   Extends Unit At: eq zero iff
-- statement:
--   The Extends Unit At construction uses the eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L216-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L216-L223

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.eq_zero_iff {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X} (h : ExtendsUnitAt s σ ξ W F t x)
    (hx : x ≫ s = spMap σ) (hW : ⊤ ≤ x ⁻¹ᵁ W) {r : ℂ} (hr : ValAt ξ x t r) : F x = 0 ↔ r = 0 := by sorry
