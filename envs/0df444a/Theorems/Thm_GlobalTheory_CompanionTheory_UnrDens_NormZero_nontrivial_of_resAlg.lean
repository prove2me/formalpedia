-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_nontrivial_of_resAlg
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormZero.nontrivial_of_resAlg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:19:54.51985+00:00
-- url     : https://prove2.me/theorems/afd60d32-8de1-41dd-8a38-aa2a2d5aa10a
-- title:
--   Norm Zero: nontrivial of res Alg
-- statement:
--   The Norm Zero construction uses the nontrivial of res Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L20-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormZero.nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by sorry
