-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIndicator_eq_of_span_col_eq
-- name    : GlobalTheory.LatticeIndicator.eq_of_span_col_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:55.318037+00:00
-- url     : https://prove2.me/theorems/649caffb-9b28-4072-9e51-b24d796873d4
-- title:
--   Lattice Indicator: eq of span col eq
-- statement:
--   The Lattice Indicator construction uses the eq of span col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L212-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L212-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator

theorem GlobalTheory.LatticeIndicator.eq_of_span_col_eq {O m n R : Type*} [CommRing O] [IsLocalRing O] [Fintype n]
    [DecidableEq n] (c : O) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) (z z' : Matrix m n O)
    (h : Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z.col j)) =
      Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z'.col j))) :
    ψ z = ψ z' := by sorry
