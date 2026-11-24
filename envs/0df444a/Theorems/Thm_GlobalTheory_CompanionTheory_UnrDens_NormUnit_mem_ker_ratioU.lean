-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_mem_ker_ratioU
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormUnit.mem_ker_ratioU
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:16.111079+00:00
-- url     : https://prove2.me/theorems/f1e5b458-4d75-4699-af05-7881f7fb9b5d
-- title:
--   Norm Unit: mem ker ratio U
-- statement:
--   The Norm Unit construction uses the mem ker ratio U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L189-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L189-L190

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

theorem GlobalTheory.CompanionTheory.UnrDens.NormUnit.mem_ker_ratioU {k : Eˣ} : k ∈ (ratioU τ).ker ↔ (k : E) = τ k := by sorry
