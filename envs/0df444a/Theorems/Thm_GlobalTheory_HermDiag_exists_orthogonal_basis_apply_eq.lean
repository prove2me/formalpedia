-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_apply_eq
-- name    : GlobalTheory.HermDiag.exists_orthogonal_basis_apply_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:49.525984+00:00
-- url     : https://prove2.me/theorems/b99b9e7f-bc89-4c0b-874f-890c9f2b5441
-- title:
--   Herm Diag: exists orthogonal basis apply eq
-- statement:
--   The Herm Diag construction uses the exists orthogonal basis apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L107-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L107-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E}
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {n : Type*} [Fintype n]

theorem GlobalTheory.HermDiag.exists_orthogonal_basis_apply_eq (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) (hn : finrank E V = Fintype.card n) {x : V}
    (hx : B x x ≠ 0) (i₀ : n) :
    ∃ v : Basis n E V, v i₀ = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by sorry
