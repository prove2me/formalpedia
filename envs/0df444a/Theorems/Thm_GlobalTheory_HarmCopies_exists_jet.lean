-- Prove2me | Theorems.Thm_GlobalTheory_HarmCopies_exists_jet
-- name    : GlobalTheory.HarmCopies.exists_jet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:44.975633+00:00
-- url     : https://prove2.me/theorems/2dd4029e-f8af-403c-bb3c-94185e61ee9e
-- title:
--   Harm Copies: exists jet
-- statement:
--   The Harm Copies construction uses the exists jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L28-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.HarmCopies
open GlobalTheory.PowGerm

theorem GlobalTheory.HarmCopies.exists_jet {k : Type} [CommRing k] {n d : ℕ} (N : ℕ) (f : PS k n d) :
    ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N →
      MvPowerSeries.coeff e f =
        MvPowerSeries.coeff e (∑ j : S, MvPowerSeries.coeff j.1 f • (MvPowerSeries.monomial j.1 1 : PS k n d)) := by sorry
