-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_image_compact_right_invariant
-- name    : GlobalTheory.T.finite_image_compact_right_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:27.464809+00:00
-- url     : https://prove2.me/theorems/19b748fc-956a-42d2-b4b9-59157ba7168e
-- title:
--   T: finite image compact right invariant
-- statement:
--   The T construction uses the finite image compact right invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactRightInvariantStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactRightInvariantStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariant
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_image_compact_right_invariant : ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ), IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) → (Gf '' K).Finite := by sorry
