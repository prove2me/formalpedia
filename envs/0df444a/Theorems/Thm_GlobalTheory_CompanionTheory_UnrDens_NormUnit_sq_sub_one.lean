-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_sq_sub_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormUnit.sq_sub_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:22.101822+00:00
-- url     : https://prove2.me/theorems/598785ae-5fd5-45df-aa00-ad91f6c30f7a
-- title:
--   Norm Unit: sq sub one
-- statement:
--   The Norm Unit construction uses the sq sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L228-L231

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormUnit.sq_sub_one (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by sorry
