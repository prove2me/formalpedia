-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_inversion_iff
-- name    : GlobalTheory.FourierChainCompare.inversion_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:00.383094+00:00
-- url     : https://prove2.me/theorems/55e1f570-7d63-4fd2-84a0-a433aa28296a
-- title:
--   Fourier Chain Compare: inversion iff
-- statement:
--   The Fourier Chain Compare construction uses the inversion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L187-L191

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

theorem GlobalTheory.FourierChainCompare.inversion_iff [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    (φ a = ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a) ↔
      φ a = ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) := by sorry
