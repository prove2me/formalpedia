-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_rm_rm
-- name    : GlobalTheory.CompanionTheory.Descent.pull_rm_rm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:26:13.525691+00:00
-- url     : https://prove2.me/theorems/42ca4b7c-9c14-410a-9f16-9e88970561a1
-- title:
--   Descent: pull rm rm
-- statement:
--   The Descent construction uses the pull rm rm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L35-L39

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

theorem GlobalTheory.CompanionTheory.Descent.pull_rm_rm (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (k : E ⥤ AffOp X) (σ : D ⥤ C) (τ : E ⥤ D) (h h')
    (h'' : ∀ T, (k.obj T).unop.1 ≤ (f.obj ((τ ⋙ σ).obj T)).unop.1) (i : ℕ) (z : Cn (f ⋙ OAff s) i) :
    pulln (rm s g k τ h') i (pulln (rm s f g σ h) i z) = pulln (rm s f k (τ ⋙ σ) h'') i z := by sorry
