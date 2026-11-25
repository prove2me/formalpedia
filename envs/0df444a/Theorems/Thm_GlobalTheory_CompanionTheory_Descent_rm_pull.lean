-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_rm_pull
-- name    : GlobalTheory.CompanionTheory.Descent.rm_pull
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:52.475386+00:00
-- url     : https://prove2.me/theorems/c82a82cd-d12d-5a13-adad-bac385cfacc7
-- title:
--   Descent: rm pull
-- statement:
--   The Descent construction uses the rm pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L31-L33

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

theorem GlobalTheory.CompanionTheory.Descent.rm_pull (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (σ : D ⥤ C) (h) (i : ℕ) (z : Cn (f ⋙ OAff s) i)
    (c : Fin (i + 1) ⥤ D) :
    pulln (rm s f g σ h) i z c = Sec.res s (h (c.obj (Fin.last i))) (z (c ⋙ σ)) := by sorry
