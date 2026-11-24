-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_muMap_tmul
-- name    : GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:34.295442+00:00
-- url     : https://prove2.me/theorems/225f3e7a-df9f-4c04-b9f9-7452181971ba
-- title:
--   One Form Coh: mu Map tmul
-- statement:
--   The One Form Coh construction uses the mu Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtendedFormNaturality.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtendedFormNaturality.lean#L72-L73

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul (f : Z1 F) (v : Glob1 F) {T T' : C} (φ : T ⟶ T') :
    muMap F (f ⊗ₜ v) T T' φ = f.1 T T' φ • v.1 T' := by sorry
