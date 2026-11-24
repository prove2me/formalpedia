-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_expand
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.wb_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:50.634518+00:00
-- url     : https://prove2.me/theorems/12c7b317-1769-4441-bebc-fefdc0745c4b
-- title:
--   Hodge Two Form: wb expand
-- statement:
--   The Hodge Two Form construction uses the wb expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L61-L73

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
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.wb_expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (a b : M) :
    wb (A := A) a b = ∑ i, ∑ j ∈ Finset.Ioi i, (L i a * L j b - L j a * L i b) • wb (A := A) (e i) (e j) := by sorry
