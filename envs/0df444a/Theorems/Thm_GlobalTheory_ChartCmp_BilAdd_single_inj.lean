-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_BilAdd_single_inj
-- name    : GlobalTheory.ChartCmp.BilAdd.single_inj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:43.141776+00:00
-- url     : https://prove2.me/theorems/79c4e052-ca6e-42bf-908e-18a98c0bd8d6
-- title:
--   Bil Add: single inj
-- statement:
--   The Bil Add construction uses the single inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L106-L112

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

theorem GlobalTheory.ChartCmp.BilAdd.single_inj {i j i' j' : Fin d}
    (h : (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1) : i = i' ∧ j = j' := by sorry
