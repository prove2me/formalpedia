-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_BilAdd_jeq_bilSer_of_biadditive
-- name    : GlobalTheory.ChartCmp.BilAdd.jeq_bilSer_of_biadditive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:34.243702+00:00
-- url     : https://prove2.me/theorems/fe3ff095-e8bf-5852-9380-ccba2f9fab18
-- title:
--   Bil Add: jeq bil Ser of biadditive
-- statement:
--   The Bil Add construction uses the jeq bil Ser of biadditive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L154-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L154-L194

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

theorem GlobalTheory.ChartCmp.BilAdd.jeq_bilSer_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by sorry
