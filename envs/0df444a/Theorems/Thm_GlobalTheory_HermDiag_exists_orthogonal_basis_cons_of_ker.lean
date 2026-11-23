-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_cons_of_ker
-- name    : GlobalTheory.HermDiag.exists_orthogonal_basis_cons_of_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:31.870055+00:00
-- url     : https://prove2.me/theorems/8159d4ba-32f1-42a5-a1da-164dc49a5a22
-- title:
--   Herm Diag: exists orthogonal basis cons of ker
-- statement:
--   The Herm Diag construction uses the exists orthogonal basis cons of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L45-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L45-L72

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

theorem GlobalTheory.HermDiag.exists_orthogonal_basis_cons_of_ker {V : Type*} [AddCommGroup V] [Module E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) {x : V} (hx : B x x ≠ 0) {d : ℕ}
    (v' : Basis (Fin d) E (LinearMap.ker (B.flip x)))
    (hv' : ∀ i j, i ≠ j → B (v' i) (v' j) = 0) :
    ∃ v : Basis (Fin (d + 1)) E V, v 0 = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by sorry
