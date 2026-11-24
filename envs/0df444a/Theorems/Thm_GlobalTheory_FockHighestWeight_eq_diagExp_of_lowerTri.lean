-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_eq_diagExp_of_lowerTri
-- name    : GlobalTheory.FockHighestWeight.eq_diagExp_of_lowerTri
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:28.0138+00:00
-- url     : https://prove2.me/theorems/3a0ca0e7-891e-42e7-86f8-0c5087a3f38a
-- title:
--   Fock Highest Weight: eq diag Exp of lower Tri
-- statement:
--   The Fock Highest Weight construction uses the eq diag Exp of lower Tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L76-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L76-L103

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

theorem GlobalTheory.FockHighestWeight.eq_diagExp_of_lowerTri (hn : n ≤ r) {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ} (hm : LowerTri m)
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hrow : Finsupp.weight (rowW r n) m = rowNu (r := r) ν) : m = diagExp r ν := by sorry
