-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_sum_annihilator
-- name    : GlobalTheory.T.tensor_sum_annihilator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:24.278785+00:00
-- url     : https://prove2.me/theorems/77501885-e07b-4497-b218-5e28069a2872
-- title:
--   T: tensor sum annihilator
-- statement:
--   The T construction uses the tensor sum annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilatorStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilatorStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensor_sum_annihilator : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by sorry
