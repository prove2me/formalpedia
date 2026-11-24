-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_fourierCoeff_eq
-- name    : GlobalTheory.FourierChainCompare.fourierCoeff_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:32.182172+00:00
-- url     : https://prove2.me/theorems/3a902f81-cfb5-496c-860b-8240fe941773
-- title:
--   Fourier Chain Compare: fourier Coeff eq
-- statement:
--   The Fourier Chain Compare construction uses the fourier Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L176-L178

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

theorem GlobalTheory.FourierChainCompare.fourierCoeff_eq {e : A → B → Kˣ} (he : IsPerfectPairing e) (φ : A → K) (t : B) :
    IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t = (Fintype.card A : K)⁻¹ * ∑ b, φ b * chr he t (-b) := by sorry
