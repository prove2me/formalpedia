-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_SameVec_unique_left
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.SameVec.unique_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:09.814928+00:00
-- url     : https://prove2.me/theorems/507e4fd1-405b-4cf3-b3d9-c9f4ca0abf2e
-- title:
--   Same Vec: unique left
-- statement:
--   The Same Vec construction uses the unique left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L102-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L102-L110

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.SameVec.unique_left {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v₁ v₂ : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v₁ v') (h₂ : SameVec Y y v₂ v') : v₁ = v₂ := by sorry
