-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_exists_finite_cover
-- name    : GlobalTheory.CompanionTheory.Descent.exists_finite_cover
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:26:49.1398+00:00
-- url     : https://prove2.me/theorems/fb08c8d2-6bd4-4946-a564-4b2540150079
-- title:
--   Descent: exists finite cover
-- statement:
--   The Descent construction uses the exists finite cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L264-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L264-L273

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
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

theorem GlobalTheory.CompanionTheory.Descent.exists_finite_cover {P : Type} (v : P → X.affineOpens) (W : X.affineOpens)
    (hcov : ⨆ a, (v a).1 = W.1) : ∃ T : Finset P, W.1 ≤ ⨆ a : T, (v a.1).1 := by sorry
