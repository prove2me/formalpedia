-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_linear_form_extension_naturality
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.linear_form_extension_naturality
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:12.520048+00:00
-- url     : https://prove2.me/theorems/b5d98268-9637-4b18-a0f5-a96495d5155b
-- title:
--   Hodge Two Form: linear form extension naturality
-- statement:
--   The Hodge Two Form construction uses the linear form extension naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L133-L138

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

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.linear_form_extension_naturality (hP : Par F) (l : Module.Dual R (Glob1 F)) {T T' : C} (φ : T ⟶ T')
    (α : Ω[F.obj T⁄R]) : Lf hP l T' (p1 F φ α) = mp F φ (Lf hP l T α) := by sorry
