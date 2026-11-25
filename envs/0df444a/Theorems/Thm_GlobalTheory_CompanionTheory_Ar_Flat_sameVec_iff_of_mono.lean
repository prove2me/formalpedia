-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_sameVec_iff_of_mono
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.sameVec_iff_of_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:22.186451+00:00
-- url     : https://prove2.me/theorems/23068d2c-2306-4fa2-b47a-03cbcfb60805
-- title:
--   Flat: same Vec iff of mono
-- statement:
--   The Flat construction uses the same Vec iff of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L112-L119

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.sameVec_iff_of_mono (Y : Model Xo c β) [Mono Y.j] {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) :
    SameVec Y y v v' ↔
      ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left := by sorry
