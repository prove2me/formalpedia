-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_compare
-- name    : GlobalTheory.CompanionTheory.Descent.compare
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:45.565112+00:00
-- url     : https://prove2.me/theorems/59f9f0d1-63c1-4ea4-8829-2ec1bf08542c
-- title:
--   Descent: compare
-- statement:
--   The Descent construction uses the compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L195-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L195-L232

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]

theorem GlobalTheory.CompanionTheory.Descent.compare (hCx : CxSt) (hQ : QCalcSt) (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D]
    (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (w : C × D ⥤ AffOp X) (σ : D ⥤ C)
    (h₁ : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1) (h₂ : ∀ T, (w.obj T).unop.1 ≤ (g.obj T.2).unop.1)
    (h₃ : ∀ d, (g.obj d).unop.1 ≤ (w.obj (σ.obj d, d)).unop.1)
    (A₁ : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h₁ (c, T)))
    (A₂ : ∀ d, Acyc s (CategoryTheory.Prod.sectR d C ⋙ CategoryTheory.Prod.swap D C ⋙ w) (g.obj d).unop.1 (fun T ↦ h₂ (T, d))) :
    AllQIso (rm s f g σ (fun d ↦ (h₃ d).trans (h₁ (σ.obj d, d)))) := by sorry
