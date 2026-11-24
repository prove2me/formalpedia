-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_eq_zero_of_trivial
-- name    : GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:15.950798+00:00
-- url     : https://prove2.me/theorems/bffa361d-41c6-48f4-a4fd-9ca581453b89
-- title:
--   Herm Orth: red eq zero of trivial
-- statement:
--   The Herm Orth construction uses the red eq zero of trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L89-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L89-L112

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by sorry
