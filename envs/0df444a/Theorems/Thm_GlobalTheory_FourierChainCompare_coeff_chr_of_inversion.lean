-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_coeff_chr_of_inversion
-- name    : GlobalTheory.FourierChainCompare.coeff_chr_of_inversion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:16.848173+00:00
-- url     : https://prove2.me/theorems/bfe34385-211e-4204-9fdc-c05e6257a30b
-- title:
--   Fourier Chain Compare: coeff chr of inversion
-- statement:
--   The Fourier Chain Compare construction uses the coeff chr of inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L193-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L193-L205

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

theorem GlobalTheory.FourierChainCompare.coeff_chr_of_inversion [DecidableEq B] {e : A → B → Kˣ} (he : IsPerfectPairing e) (t₀ : B)
    (h : ∀ a, ((e a t₀ : Kˣ) : K) =
      ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t * ((e a t : Kˣ) : K)) (t : B) :
    IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t = if t = t₀ then 1 else 0 := by sorry
