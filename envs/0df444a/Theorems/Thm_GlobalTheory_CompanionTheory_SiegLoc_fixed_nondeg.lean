-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_fixed_nondeg
-- name    : GlobalTheory.CompanionTheory.SiegLoc.fixed_nondeg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:42.514832+00:00
-- url     : https://prove2.me/theorems/22712e9a-7149-46ef-ac7f-8f6dc0f19090
-- title:
--   Sieg Loc: fixed nondeg
-- statement:
--   The Sieg Loc construction uses the fixed nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FixedNondeg.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FixedNondeg.lean#L23-L44

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by sorry
