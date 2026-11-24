-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_quasiRefl
-- name    : GlobalTheory.HermWitt.quasiRefl_quasiRefl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:32.616496+00:00
-- url     : https://prove2.me/theorems/3738c9aa-ddae-4912-bac5-7243b925b532
-- title:
--   Herm Witt: quasi Refl quasi Refl
-- statement:
--   The Herm Witt construction uses the quasi Refl quasi Refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L19-L26

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

theorem GlobalTheory.HermWitt.quasiRefl_quasiRefl (B : V →ₗ[E] V →ₛₗ[c] E) {v : V} {a b : E} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b = B v v) (z : V) : quasiRefl B v b (quasiRefl B v a z) = z := by sorry
