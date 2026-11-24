-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_gram_expand
-- name    : GlobalTheory.CompanionTheory.UnrDens.HenselStep.gram_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:20:48.74421+00:00
-- url     : https://prove2.me/theorems/f0f86324-5797-4104-aded-d17d4b94b421
-- title:
--   Hensel Step: gram expand
-- statement:
--   The Hensel Step construction uses the gram expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean#L103-L109

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

theorem GlobalTheory.CompanionTheory.UnrDens.HenselStep.gram_expand (σ : R →+* R) {r : R} (hc : σ r = r) (S : Matrix (Fin a) (Fin a) R)
    (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + r • y) * S * (x + r • y) =
      cT σ x * S * x + r • (cT σ y * S * x + cT σ x * S * y) + (r * r) • (cT σ y * S * y) := by sorry
