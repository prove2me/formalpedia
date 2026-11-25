-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_WedgeField_vb_of_bijective
-- name    : GlobalTheory.CompanionTheory.Hodge.WedgeField.vb_of_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:45.832996+00:00
-- url     : https://prove2.me/theorems/e69b7d65-0794-5d2a-adf7-c91b6296d00e
-- title:
--   Wedge Field: vb of bijective
-- statement:
--   The Wedge Field construction uses the vb of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfBijective.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfBijective.lean#L65-L72

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem GlobalTheory.CompanionTheory.Hodge.WedgeField.vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by sorry
