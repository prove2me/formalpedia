-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_fixed_decomp
-- name    : GlobalTheory.CompanionTheory.SiegLoc.Scaled.fixed_decomp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:35.6728+00:00
-- url     : https://prove2.me/theorems/354986fd-daed-40db-9f60-e441dbdec637
-- title:
--   Scaled: fixed decomp
-- statement:
--   The Scaled construction uses the fixed decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L20-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardRangeMulQuotientBoundedLevel.lean#L20-L38

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

theorem GlobalTheory.CompanionTheory.SiegLoc.Scaled.fixed_decomp {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    (k : ℕ) (d : R) (hd : σ d = d) :
    d ∈ lev ϖ k ∨ ∃ a₀ e c, k = e + a₀ ∧ σ c = c ∧ c ∉ lev ϖ 1 ∧ d = ϖ ^ a₀ * c := by sorry
