-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_aug
-- name    : GlobalTheory.CompanionTheory.Descent.pull_aug
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:54.367813+00:00
-- url     : https://prove2.me/theorems/e914826b-dbc3-48b6-b2fd-d1dec8f8f647
-- title:
--   Descent: pull aug
-- statement:
--   The Descent construction uses the pull aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L108-L112

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

theorem GlobalTheory.CompanionTheory.Descent.pull_aug (f : D ⥤ AffOp X) (f' : E ⥤ AffOp X) (σ : E ⥤ D) (h) (W : X.Opens) (hle hle')
    (w : Sec s W) :
    pulln (rm s f f' σ h) 0 (aug s f W hle w) = aug s f' W hle' w := by sorry
