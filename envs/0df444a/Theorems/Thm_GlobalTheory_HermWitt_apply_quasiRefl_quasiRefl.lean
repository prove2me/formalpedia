-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_apply_quasiRefl_quasiRefl
-- name    : GlobalTheory.HermWitt.apply_quasiRefl_quasiRefl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:06.134631+00:00
-- url     : https://prove2.me/theorems/dac2753a-b798-4189-a958-66a9e745fbee
-- title:
--   Herm Witt: apply quasi Refl quasi Refl
-- statement:
--   The Herm Witt construction uses the apply quasi Refl quasi Refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

theorem GlobalTheory.HermWitt.apply_quasiRefl_quasiRefl {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    {v : V} {a : E} (ha : a ≠ 0) (hab : a + c a = B v v) (z w : V) :
    B (quasiRefl B v a z) (quasiRefl B v a w) = B z w := by sorry
