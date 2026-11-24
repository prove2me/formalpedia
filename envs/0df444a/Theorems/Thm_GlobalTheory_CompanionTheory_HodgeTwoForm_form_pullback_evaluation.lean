-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_form_pullback_evaluation
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.form_pullback_evaluation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:55.591316+00:00
-- url     : https://prove2.me/theorems/9a041f16-83b0-4fa1-940d-4820d0c7cd79
-- title:
--   Hodge Two Form: form pullback evaluation
-- statement:
--   The Hodge Two Form construction uses the form pullback evaluation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L130-L131

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

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.form_pullback_evaluation {T T' : C} (φ : T ⟶ T') (x : Glob1 F) : p1 F φ (evForm F T x) = evForm F T' x := by sorry
