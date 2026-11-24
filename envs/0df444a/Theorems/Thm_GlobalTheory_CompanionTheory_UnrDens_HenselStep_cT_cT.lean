-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_cT
-- name    : GlobalTheory.CompanionTheory.UnrDens.HenselStep.cT_cT
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:42.128647+00:00
-- url     : https://prove2.me/theorems/926d3b5f-a9de-4f1b-90f2-a94f267358bb
-- title:
--   Hensel Step: c T c T
-- statement:
--   The Hensel Step construction uses the c T c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L47-L49

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

theorem GlobalTheory.CompanionTheory.UnrDens.HenselStep.cT_cT (σ : R →+* R) (h : ∀ r, σ (σ r) = r) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by sorry
