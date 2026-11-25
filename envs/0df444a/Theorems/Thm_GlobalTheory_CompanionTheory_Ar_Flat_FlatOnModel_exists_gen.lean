-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_FlatOnModel_exists_gen
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.FlatOnModel.exists_gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:14.960806+00:00
-- url     : https://prove2.me/theorems/f01152a8-1d15-4d88-a96d-1486e59a1dea
-- title:
--   Flat On Model: exists gen
-- statement:
--   The Flat On Model construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L171-L174

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.FlatOnModel.exists_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧
      Represents Y U τ Z.M a b φ := by sorry
