-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_card_range_mul
-- name    : GlobalTheory.CompanionTheory.SiegLoc.Scaled.card_range_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:31.580612+00:00
-- url     : https://prove2.me/theorems/ef8eb5e3-efb5-4b6b-b97d-88b9b41f4a55
-- title:
--   Scaled: card range mul
-- statement:
--   The Scaled construction uses the card range mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L63-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L63-L98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.Scaled
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.Scaled.card_range_mul {ϖ c : R} (hreg : IsSMulRegular R ϖ) (hc : IsUnit c) (e a₀ : ℕ) :
    Nat.card (Set.range fun w : R ⧸ lev ϖ (e + a₀) =>
      w * Ideal.Quotient.mk (lev ϖ (e + a₀)) (ϖ ^ a₀ * c)) = Nat.card (R ⧸ lev ϖ e) := by sorry
