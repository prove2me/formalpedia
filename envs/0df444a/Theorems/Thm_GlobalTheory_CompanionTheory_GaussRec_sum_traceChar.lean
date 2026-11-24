-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_traceChar
-- name    : GlobalTheory.CompanionTheory.GaussRec.sum_traceChar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:47.024642+00:00
-- url     : https://prove2.me/theorems/5d8b6259-8efa-4657-8893-ae6c4bb94571
-- title:
--   Gauss Rec: sum trace Char
-- statement:
--   The Gauss Rec construction uses the sum trace Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L69-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L69-L93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.GaussRec.sum_traceChar {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [Fintype (R ⧸ lev ϖ 1)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (c : R)
    [Decidable (c ∈ lev ϖ 1)] :
    ∑ t, traceChar σ ϖ hR.fix_ϖ ψ c t
      = if c ∈ lev ϖ 1 then (Fintype.card (R ⧸ lev ϖ 1) : ℂ) else 0 := by sorry
