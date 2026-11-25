-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_weightedHomogeneous_homogenisation
-- name    : GlobalTheory.T.exists_weightedHomogeneous_homogenisation
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:57.109149+00:00
-- url     : https://prove2.me/theorems/e3a5148e-909a-456c-b429-c551b957bb4b
-- title:
--   T: exists weighted Homogeneous homogenisation
-- statement:
--   The T construction uses the exists weighted Homogeneous homogenisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeightedHomogenisationStatement.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeightedHomogenisationStatement.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeightedHomogenisation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeightedHomogenisationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_weightedHomogeneous_homogenisation : ∀ {L : Type} [Field L] (Q : Subring L) (r : ℕ) (z : Fin (r + 1) → Q)
    (wt : Fin (r + 1) → ℕ), wt 0 = 1 → (z 0 : L) ≠ 0 → ∀ P : MvPolynomial (Fin r) Q,
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by sorry
