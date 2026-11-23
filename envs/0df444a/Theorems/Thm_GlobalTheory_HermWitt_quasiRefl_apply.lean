-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_apply
-- name    : GlobalTheory.HermWitt.quasiRefl_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:42.025441+00:00
-- url     : https://prove2.me/theorems/73208891-6619-434f-94ed-c725e149a005
-- title:
--   Herm Witt: quasi Refl apply
-- statement:
--   The Herm Witt construction uses the quasi Refl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L15-L17

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

theorem GlobalTheory.HermWitt.quasiRefl_apply (B : V →ₗ[E] V →ₛₗ[c] E) (v : V) (a : E) (z : V) :
    quasiRefl B v a z = z - (a⁻¹ * B z v) • v := by sorry
