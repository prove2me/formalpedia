-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_BilAdd_ev_pair
-- name    : GlobalTheory.ChartCmp.BilAdd.ev_pair
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:10:22.144508+00:00
-- url     : https://prove2.me/theorems/08a8a997-5fa3-5bdf-9766-f245a2104d29
-- title:
--   Bil Add: ev pair
-- statement:
--   The Bil Add construction uses the ev pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L142-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.BilAdd
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.ChartCmp.BilAdd.ev_pair (b : Fin 3 → Pt k 2 d) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (g : PS k 2 d)
    (u v : Pt k 3 d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) :
    ev b (ev ![u, v] g) = ev ![fun i => ev b (u i), fun i => ev b (v i)] g := by sorry
