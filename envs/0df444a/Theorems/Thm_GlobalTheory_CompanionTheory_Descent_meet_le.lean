-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_meet_le
-- name    : GlobalTheory.CompanionTheory.Descent.meet_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:26:14.245866+00:00
-- url     : https://prove2.me/theorems/031f0fa9-9590-4ac6-b298-28259603c7df
-- title:
--   Descent: meet le
-- statement:
--   The Descent construction uses the meet le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L242-L245

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

theorem GlobalTheory.CompanionTheory.Descent.meet_le {U U' V V' : X.affineOpens} (h : U.1 ≤ U'.1) (h' : V.1 ≤ V'.1) :
    meet hi U V ≤ meet hi U' V' := by sorry
