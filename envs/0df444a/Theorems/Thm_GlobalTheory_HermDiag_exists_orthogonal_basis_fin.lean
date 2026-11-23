-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_fin
-- name    : GlobalTheory.HermDiag.exists_orthogonal_basis_fin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:59.326931+00:00
-- url     : https://prove2.me/theorems/44b54bcf-ec05-424f-8a19-bf3a072d08cf
-- title:
--   Herm Diag: exists orthogonal basis fin
-- statement:
--   The Herm Diag construction uses the exists orthogonal basis fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L76-L94

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
universe u in

theorem GlobalTheory.HermDiag.exists_orthogonal_basis_fin (h2 : (2 : E) ≠ 0) (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (B : V →ₗ[E] V →ₛₗ[c] E), (∀ x y, c (B x y) = B y x) → finrank E V = d →
      ∃ v : Basis (Fin d) E V, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by sorry
