-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_eq_diagExp_of_offDiag
-- name    : GlobalTheory.FockHighestWeight.eq_diagExp_of_offDiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:13.796507+00:00
-- url     : https://prove2.me/theorems/8c660cf9-43a4-4789-9573-542be30b62fa
-- title:
--   Fock Highest Weight: eq diag Exp of off Diag
-- statement:
--   The Fock Highest Weight construction uses the eq diag Exp of off Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L42-L54

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
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
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}

theorem GlobalTheory.FockHighestWeight.eq_diagExp_of_offDiag {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ}
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hoff : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0) : m = diagExp r ν := by sorry
