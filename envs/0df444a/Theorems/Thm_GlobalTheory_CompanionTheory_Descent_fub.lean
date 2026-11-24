-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_fub
-- name    : GlobalTheory.CompanionTheory.Descent.fub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:36.931959+00:00
-- url     : https://prove2.me/theorems/59fe2905-e7c8-40be-a6d3-2f3748fa1ed4
-- title:
--   Descent: fub
-- statement:
--   The Descent construction uses the fub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L189-L193

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

theorem GlobalTheory.CompanionTheory.Descent.fub (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D] (f : C ⥤ AffOp X) (w : C × D ⥤ AffOp X)
    (h : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1)
    (A : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h (c, T))) :
    AllQIso (rm s f w (CategoryTheory.Prod.fst C D) h) := by sorry
