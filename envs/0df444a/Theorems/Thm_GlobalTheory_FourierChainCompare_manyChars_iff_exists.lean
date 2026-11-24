-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_iff_exists
-- name    : GlobalTheory.FourierChainCompare.manyChars_iff_exists
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:13.991185+00:00
-- url     : https://prove2.me/theorems/625ccf3f-7741-4300-98d4-2d011800d74a
-- title:
--   Fourier Chain Compare: many Chars iff exists
-- statement:
--   The Fourier Chain Compare construction uses the many Chars iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L160-L168

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
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
variable [Fintype A] [Fintype B]

theorem GlobalTheory.FourierChainCompare.manyChars_iff_exists (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
      IsPerfectPairing e := by sorry
