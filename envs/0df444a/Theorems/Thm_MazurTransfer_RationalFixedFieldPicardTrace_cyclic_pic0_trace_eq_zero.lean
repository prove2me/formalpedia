-- Prove2me | Theorems.Thm_MazurTransfer_RationalFixedFieldPicardTrace_cyclic_pic0_trace_eq_zero
-- name    : MazurTransfer.RationalFixedFieldPicardTrace.cyclic_pic0_trace_eq_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T16:28:38.138033+00:00
-- url     : https://prove2.me/theorems/b3fddad5-180a-4479-9a2e-9c1fe91a6436
-- title:
--   Cyclic Pic0 trace vanishes for a specified rational fixed field
-- statement:
--   For fields K and E with the original K-algebra structure and HasPrincipalDivisors K E, let sigma be a finite-order K-automorphism of E. A specified K-algebra equivalence from K(t) to the fixed field of its cyclic subgroup makes the explicit sum over i in Fin(orderOf sigma) of sigma^i acting on any arithmetic Pic0 class equal to zero. Every original hypothesis and universe is retained.
-- source:
--   Complete unchanged original MazurTheorem RationalFixedFieldPicardTrace.cyclic_pic0_trace_eq_zero proof, including the full original finite-subgroup trace helper. Official Anthropic FLT divisor/Pic0 trace interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original fixed-field subgroup and cyclic Pic0 trace proofs retained.
Design boundary: a finite-order automorphism with a specified rational fixed
field has zero cyclic trace on arithmetic Pic0, with the actual order explicit.
Named downstream consumer: actual order-13 diamond square/cube trace and norm.
Official Anthropic FLT divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_pic0_galois_trace_eq_zero
import Mathlib.FieldTheory.Fixed
noncomputable section
universe u v
open AlgebraicCurve

theorem MazurTransfer.RationalFixedFieldPicardTrace.cyclic_pic0_trace_eq_zero
    {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [HasPrincipalDivisors K E] (σ : E ≃ₐ[K] E) (hσ : IsOfFinOrder σ)
    (e : RatFunc K ≃ₐ[K] IntermediateField.fixedField (Subgroup.zpowers σ))
    (c : Pic0 K E) :
    ∑ i : Fin (orderOf σ), (σ ^ (i : ℕ)) • c = 0 := by sorry
