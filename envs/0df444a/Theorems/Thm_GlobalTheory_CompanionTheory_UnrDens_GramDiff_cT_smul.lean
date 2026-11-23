-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_cT_smul
-- name    : GlobalTheory.CompanionTheory.UnrDens.GramDiff.cT_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:54.016879+00:00
-- url     : https://prove2.me/theorems/1b16dbd5-68af-49bb-85ee-ce6c6992a616
-- title:
--   Gram Diff: c T smul
-- statement:
--   The Gram Diff construction uses the c T smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFibreGramDifferential.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFibreGramDifferential.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.GramDiff
variable {E : Type} [CommRing E] (τ : E →+* E)

theorem GlobalTheory.CompanionTheory.UnrDens.GramDiff.cT_smul {a b : ℕ} (c : E) (A : Matrix (Fin a) (Fin b) E) :
    cT τ (c • A) = τ c • cT τ A := by sorry
