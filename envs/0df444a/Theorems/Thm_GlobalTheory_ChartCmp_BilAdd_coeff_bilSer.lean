-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_BilAdd_coeff_bilSer
-- name    : GlobalTheory.ChartCmp.BilAdd.coeff_bilSer
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:59.762017+00:00
-- url     : https://prove2.me/theorems/80cab5a9-bf51-4f3f-8936-b948761ce8a3
-- title:
--   Bil Add: coeff bil Ser
-- statement:
--   The Bil Add construction uses the coeff bil Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L99-L104

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

theorem GlobalTheory.ChartCmp.BilAdd.coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (bilSer β (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      ∑ i, ∑ j, if e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 then β i j else 0 := by sorry
