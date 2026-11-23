-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_IsFlatAn_const_mul
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.IsFlatAn.const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:51.271587+00:00
-- url     : https://prove2.me/theorems/ab35bf13-9546-4161-9513-86d4983587f9
-- title:
--   Is Flat An: const mul
-- statement:
--   The Is Flat An construction uses the const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L192-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean#L192-L198

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.IsFlatAn.const_mul {U : Set (Xo.XF c)} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} {σK : KA l →+* ℂ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo σK ty} {i : Fin FU.n}
    {e : Fin D.p ⊕ Fin D.q → (FU.Di i).La} {ρ : ℂ} (h : IsFlatAn U τ τ' σ Φ FU i e ρ) (k : ℂ) :
    IsFlatAn U τ τ' σ (fun y v w => k * Φ y v w) FU i e (k * ρ) := by sorry
