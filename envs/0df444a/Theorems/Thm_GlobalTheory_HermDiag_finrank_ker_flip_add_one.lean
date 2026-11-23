-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_finrank_ker_flip_add_one
-- name    : GlobalTheory.HermDiag.finrank_ker_flip_add_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:26.838805+00:00
-- url     : https://prove2.me/theorems/22493b47-234c-4c75-ad43-1b23497456ec
-- title:
--   Herm Diag: finrank ker flip add one
-- statement:
--   The Herm Diag construction uses the finrank ker flip add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L33-L43

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

theorem GlobalTheory.HermDiag.finrank_ker_flip_add_one {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} {x : V} (hx : B x x ≠ 0) :
    finrank E (LinearMap.ker (B.flip x)) + 1 = finrank E V := by sorry
