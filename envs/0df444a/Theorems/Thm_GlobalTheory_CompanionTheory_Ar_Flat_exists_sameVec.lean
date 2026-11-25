-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_exists_sameVec
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.exists_sameVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:25.564161+00:00
-- url     : https://prove2.me/theorems/67253e15-2fc8-4c2a-ad34-fc3d38077046
-- title:
--   Flat: exists same Vec
-- statement:
--   The Flat construction uses the exists same Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L68-L77

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) : ∃ v', SameVec Y y v v' := by sorry
