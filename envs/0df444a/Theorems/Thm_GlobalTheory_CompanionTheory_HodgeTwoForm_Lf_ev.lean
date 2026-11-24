-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_ev
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_ev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:00.062368+00:00
-- url     : https://prove2.me/theorems/68c7f50e-2914-4ba0-b1ba-d9dcfeaa60e8
-- title:
--   Hodge Two Form: Lf ev
-- statement:
--   The Hodge Two Form construction uses the Lf ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L126-L128

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_ev (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) (x : Glob1 F) :
    Lf hP l T (evForm F T x) = algebraMap R (F.obj T) (l x) := by sorry
