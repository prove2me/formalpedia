-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFinite_finite_of_triangular
-- name    : GlobalTheory.LaurentFinite.finite_of_triangular
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:25.89842+00:00
-- url     : https://prove2.me/theorems/43839cf0-213e-4962-8d66-066ce1603bd8
-- title:
--   Laurent Finite: finite of triangular
-- statement:
--   The Laurent Finite construction uses the finite of triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L78-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L78-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra

theorem GlobalTheory.LaurentFinite.finite_of_triangular (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ)))
    (hB : ∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧
      ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) :
    Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by sorry
