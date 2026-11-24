-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_mem_inV
-- name    : GlobalTheory.WeylDuality.mem_inV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:47.395535+00:00
-- url     : https://prove2.me/theorems/bc498283-0674-4c92-b1f4-172e516c7023
-- title:
--   Weyl Duality: mem in V
-- statement:
--   The Weyl Duality construction uses the mem in V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L223-L225

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

theorem GlobalTheory.WeylDuality.mem_inV {r n : ℕ} (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (x : dualWeyl ℚ r n ν) : x ∈ inV ν M ↔ x.1 ∈ M := by sorry
