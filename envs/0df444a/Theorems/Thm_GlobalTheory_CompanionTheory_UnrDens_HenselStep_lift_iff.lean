-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_lift_iff
-- name    : GlobalTheory.CompanionTheory.UnrDens.HenselStep.lift_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:20:33.375037+00:00
-- url     : https://prove2.me/theorems/69a29679-528a-4bfb-a24c-bd9f268cb5fe
-- title:
--   Hensel Step: lift iff
-- statement:
--   The Hensel Step construction uses the lift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L111-L126

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
variable {R : Type} [CommRing R] {a b c : ℕ}

theorem GlobalTheory.CompanionTheory.UnrDens.HenselStep.lift_iff {σ : R →+* R} {ϖ : R} (hf : σ ϖ = ϖ) (hr : IsSMulRegular R ϖ) {k : ℕ} (hk : 1 ≤ k)
    (S : Matrix (Fin a) (Fin a) R) (T H : Matrix (Fin b) (Fin b) R)
    (x y : Matrix (Fin a) (Fin b) R) (hH : cT σ x * S * x + ϖ ^ k • H = T) :
    red ϖ (k + 1) (cT σ (x + ϖ ^ k • y) * S * (x + ϖ ^ k • y)) = red ϖ (k + 1) T ↔
      red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 H := by sorry
