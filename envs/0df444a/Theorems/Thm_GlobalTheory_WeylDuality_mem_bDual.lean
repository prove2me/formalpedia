-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_mem_bDual
-- name    : GlobalTheory.WeylDuality.mem_bDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:05.911514+00:00
-- url     : https://prove2.me/theorems/57c7b597-96bb-40eb-8e76-04be87ad2317
-- title:
--   Weyl Duality: mem b Dual
-- statement:
--   The Weyl Duality construction uses the mem b Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L88-L92

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.mem_bDual {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) :
    P ∈ bDual r n hn ν M ↔
      P ∈ dualWeyl ℚ r n ν ∧ ∀ Q ∈ M, ∃ z : ℤ, fockQ P Q = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by sorry
