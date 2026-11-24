-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_two_form_naturality
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_two_form_naturality
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:04.001477+00:00
-- url     : https://prove2.me/theorems/7a14afd4-b2ec-4380-aae1-c6dad4611b0f
-- title:
--   Hodge Two Form: wedge functional two form naturality
-- statement:
--   The Hodge Two Form construction uses the wedge functional two form naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L151-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L151-L163

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

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_two_form_naturality (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) {T T' : C}
    (φ : T ⟶ T') (z : Om R (F.obj T) 2) :
    L2 (fun i ↦ Lf hP (l i) T') i j (pOm F 2 φ z) = mp F φ (L2 (fun i ↦ Lf hP (l i) T) i j z) := by sorry
