-- Prove2me | Theorems.Thm_GlobalTheory_FourierChainCompare_inversionSum_eq
-- name    : GlobalTheory.FourierChainCompare.inversionSum_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:25.699798+00:00
-- url     : https://prove2.me/theorems/8445f6bb-b43e-4244-9dbc-69f9633baaf0
-- title:
--   Fourier Chain Compare: inversion Sum eq
-- statement:
--   The Fourier Chain Compare construction uses the inversion Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean#L180-L185

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

theorem GlobalTheory.FourierChainCompare.inversionSum_eq [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) =
      ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a := by sorry
