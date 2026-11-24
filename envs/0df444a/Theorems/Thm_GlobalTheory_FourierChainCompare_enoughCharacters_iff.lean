-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_enoughCharacters_iff
-- name    : GlobalTheory.FourierChainCompare.enoughCharacters_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:41.992063+00:00
-- url     : https://prove2.me/theorems/d92cc353-2180-40cc-84dc-9402a29e2611
-- title:
--   Fourier Chain Compare: enough Characters iff
-- statement:
--   The Fourier Chain Compare construction uses the enough Characters iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L226-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L226-L230

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
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]

theorem GlobalTheory.FourierChainCompare.enoughCharacters_iff : EnoughCharacters ↔
    ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K := by sorry
