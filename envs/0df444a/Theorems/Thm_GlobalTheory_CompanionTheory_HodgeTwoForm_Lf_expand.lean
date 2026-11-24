-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_expand
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_expand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:27.080305+00:00
-- url     : https://prove2.me/theorems/5c2b8ab6-908f-4a7f-ad5f-9872d8af1a68
-- title:
--   Hodge Two Form: Lf expand
-- statement:
--   The Hodge Two Form construction uses the Lf expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L140-L149

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

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_expand (hP : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Module.Dual R (Glob1 F))
    (h : ∀ x, x = ∑ i, l i x • w i) (T : C) (α : Ω[F.obj T⁄R]) :
    α = ∑ i, Lf hP (l i) T α • evForm F T (w i) := by sorry
