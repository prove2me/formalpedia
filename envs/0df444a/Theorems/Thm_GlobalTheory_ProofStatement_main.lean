-- Prove2me | Theorems.Thm_GlobalTheory_ProofStatement_main
-- name    : GlobalTheory.ProofStatement.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:51.332153+00:00
-- url     : https://prove2.me/theorems/f1b5596e-3a03-4e76-a6d7-f98e6765de24
-- title:
--   Proof Statement: main
-- statement:
--   The Proof Statement construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsBisAlt.lean#L5-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsBisAlt.lean#L5-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProofStatement

theorem GlobalTheory.ProofStatement.main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by sorry
