-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_orthonormal_tuples
-- name    : GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:00.063366+00:00
-- url     : https://prove2.me/theorems/6f72c9aa-c9e6-42f5-b696-b192ef0faaca
-- title:
--   Unr Dens: card orthonormal tuples
-- statement:
--   The Unr Dens construction uses the card orthonormal tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardOrthonormalFramesHermitianSpace.lean#L49-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardOrthonormalFramesHermitianSpace.lean#L49-L89

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
open OrthCount

theorem GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by sorry
