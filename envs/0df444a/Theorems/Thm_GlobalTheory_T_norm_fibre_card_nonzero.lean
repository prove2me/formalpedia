-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_fibre_card_nonzero
-- name    : GlobalTheory.T.norm_fibre_card_nonzero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:12.129139+00:00
-- url     : https://prove2.me/theorems/33e1f5c5-c782-4139-ba4a-ff7873fbb40d
-- title:
--   T: norm fibre card nonzero
-- statement:
--   The T construction uses the norm fibre card nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_fibre_card_nonzero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by sorry
