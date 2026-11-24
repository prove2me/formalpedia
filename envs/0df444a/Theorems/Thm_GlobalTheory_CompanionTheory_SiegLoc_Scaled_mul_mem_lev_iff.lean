-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_mul_mem_lev_iff
-- name    : GlobalTheory.CompanionTheory.SiegLoc.Scaled.mul_mem_lev_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:42.637672+00:00
-- url     : https://prove2.me/theorems/eeb06e0a-c6fa-4e25-9752-4537a71fecef
-- title:
--   Scaled: mul mem lev iff
-- statement:
--   The Scaled construction uses the mul mem lev iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L45-L61

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

theorem GlobalTheory.CompanionTheory.SiegLoc.Scaled.mul_mem_lev_iff {ϖ c : R} (hreg : IsSMulRegular R ϖ) (hc : IsUnit c) (e a₀ : ℕ) (y : R) :
    ϖ ^ a₀ * c * y ∈ lev ϖ (e + a₀) ↔ y ∈ lev ϖ e := by sorry
