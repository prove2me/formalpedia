-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_sum_decay_bound
-- name    : GlobalTheory.T.lattice_sum_decay_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:37.867545+00:00
-- url     : https://prove2.me/theorems/4a04f96e-0e38-5e5a-a38d-594012f5f801
-- title:
--   T: lattice sum decay bound
-- statement:
--   The T construction uses the lattice sum decay bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_sum_decay_bound : ∀ {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ), (∀ p, 0 < b p) → ∀ (h : S → ℝ≥0∞), Set.InjOn m {ξ | h ξ ≠ 0} → (∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) → ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by sorry
