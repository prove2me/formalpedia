-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_integrable_of_summable_quotient_periodic
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:53.70915+00:00
-- url     : https://prove2.me/theorems/74f30229-825b-4f9d-b882-2abb4b192d1b
-- title:
--   Integ: integrable of summable quotient periodic
-- statement:
--   The Integ construction uses the integrable of summable quotient periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOverLatticeQuotientLocallyConstant.lean#L7-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOverLatticeQuotientLocallyConstant.lean#L7-L95

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOverLatticeQuotientLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by sorry
