-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_SameVec_unique
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.SameVec.unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:42.870691+00:00
-- url     : https://prove2.me/theorems/207401f1-c2be-4156-bc47-59131382b6f2
-- title:
--   Same Vec: unique
-- statement:
--   The Same Vec construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L92-L100

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.SameVec.unique {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v₁ v₂ : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v v₁) (h₂ : SameVec Y y v v₂) : v₁ = v₂ := by sorry
