-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JCalc_jeq_calculus
-- name    : GlobalTheory.ChartCmp.JCalc.jeq_calculus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:57.723168+00:00
-- url     : https://prove2.me/theorems/6b2c75c6-a957-4753-872e-e108eb772638
-- title:
--   JCalc: jeq calculus
-- statement:
--   The JCalc construction uses the jeq calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesJetEqCalculus.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesJetEqCalculus.lean#L100-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JCalc
variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

theorem GlobalTheory.ChartCmp.JCalc.jeq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) := by sorry
