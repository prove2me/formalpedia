-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_act_zero
-- name    : GlobalTheory.FourierChainCompare.act_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:38.129958+00:00
-- url     : https://prove2.me/theorems/65d2503c-c79c-49ee-85af-16fc0145dbc8
-- title:
--   Fourier Chain Compare: act zero
-- statement:
--   The Fourier Chain Compare construction uses the act zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L306-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L306-L333

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.FourierChainCompare.act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by sorry
