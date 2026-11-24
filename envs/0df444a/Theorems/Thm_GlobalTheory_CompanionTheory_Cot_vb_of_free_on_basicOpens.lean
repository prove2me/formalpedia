-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cot_vb_of_free_on_basicOpens
-- name    : GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:58.054983+00:00
-- url     : https://prove2.me/theorems/dd45a079-3111-4935-9806-399dc21ce75b
-- title:
--   Cot: vb of free on basic Opens
-- statement:
--   The Cot construction uses the vb of free on basic Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VectorBundleOfLocalFreeness.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VectorBundleOfLocalFreeness.lean#L7-L46

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreeness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cot

theorem GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ),
      (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by sorry
