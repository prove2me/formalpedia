-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_trace_eq_of_apply_self_eq
-- name    : GlobalTheory.LocalQuad.TraceIsometry.trace_eq_of_apply_self_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:47.606092+00:00
-- url     : https://prove2.me/theorems/4b598ce6-4e09-41e6-8152-3600c30168c5
-- title:
--   Trace Isometry: trace eq of apply self eq
-- statement:
--   The Trace Isometry construction uses the trace eq of apply self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L65-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}

theorem GlobalTheory.LocalQuad.TraceIsometry.trace_eq_of_apply_self_eq {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W]
    [Module E W] {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} {φ : V → W}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x, B' (φ x) (φ x) = B x x) (x y : V) :
    B' (φ x) (φ y) + B' (φ y) (φ x) = B x y + B y x := by sorry
